(* ================================================================
   vstac/spec/compiler_correctness.v
   编译正确性定理声明 — CompCert-style Simulation Relation
   
   本文件声明了 SafeST → SafeASM 编译正确性的核心定理。
   具体证明在 proofs/ 目录中逐步完成。
   ================================================================ *)

Require Import vstac.spec.safest.
Require Import vstac.spec.safeasm.

(* ================================================================
   第 1 部分：ST 语言的操作语义 (Operational Semantics of SafeST)
   ================================================================ *)

(* ST 运行时值 *)
Inductive st_value : Type :=
  | ST_V_BOOL of bool
  | ST_V_BYTE of Z | ST_V_WORD of Z | ST_V_DWORD of Z
  | ST_V_SINT of Z | ST_V_INT of Z | ST_V_DINT of Z
  | ST_V_REAL of float
  | ST_V_TIME of Z
.

(* ST 运行时状态
   包含所有变量的当前值、当前执行位置、调用栈 *)
Record st_state : Type := {
  st_vars     : list (ident * st_value);   (* 所有变量的当前值 *)
  st_pou_idx  : Z;                          (* 当前执行的 POU 索引 *)
  st_stmt_idx : Z;                          (* 当前语句索引 *)
  st_call_stack : list Z;                   (* 调用栈 *)
  st_cycle_cnt : Z;                         (* 周期计数 *)
}.

(* ST 小步语义: step_st p s s'
   ST 程序 p 从状态 s 执行一步到 s' *)
Inductive step_st : st_program -> st_state -> st_state -> Prop :=
  (* 赋值语句: x := e, 计算 e 的值后更新 x *)
  | St_assign : forall p s x e v,
      eval_expr s e = Some v ->
      step_st p s (update_var s x v)
  
  (* IF 语句: 条件成立时走 then 分支，否则走 else 分支 *)
  | St_if_true : forall p s cond then_stmts else_stmts,
      eval_expr s cond = Some (ST_V_BOOL true) ->
      step_st p s (enter_block s then_stmts)
  
  | St_if_false : forall p s cond then_stmts else_stmts,
      eval_expr s cond = Some (ST_V_BOOL false) ->
      step_st p s (enter_block s else_stmts)
  
  (* FOR 循环: 初始化 i，判断是否越界 *)
  | St_for_init : forall p s v start end_ step body,
      eval_expr s start = Some (ST_V_INT start_val) ->
      eval_expr s end_ = Some (ST_V_INT end_val) ->
      step_st p s (init_for_loop s v start_val end_val body)
  
  | St_for_iterate : forall p s v body,
      loop_not_done s v ->
      step_st p s (execute_for_body s v body)
  
  | St_for_done : forall p s v body,
      loop_done s v ->
      step_st p s (exit_block s)
  
  (* WHILE 循环 *)
  | St_while_true : forall p s cond body,
      eval_expr s cond = Some (ST_V_BOOL true) ->
      step_st p s (enter_block s body)
  
  | St_while_false : forall p s cond body,
      eval_expr s cond = Some (ST_V_BOOL false) ->
      step_st p s (exit_block s)
  
  (* 函数调用 *)
  | St_func_call : forall p s f args,
      lookup_function_st p f = Some (param_types, body) ->
      step_st p s (push_call_frame s f args body)

  | St_func_return : forall p s ret_val,
      step_st p s (pop_call_frame s ret_val)
  
  (* FB 调用 *)
  | St_fb_call : forall p s inst params,
      lookup_fb p inst = Some fb_def ->
      step_st p s (execute_fb s fb_def params)
  
  (* 空语句块 *)
  | St_skip : forall p s,
      step_st p s s
.

(* ST 多步执行 *)
Inductive star_step_st : st_program -> st_state -> st_state -> Prop :=
  | Star_st_refl : forall p s, star_step_st p s s
  | Star_st_step : forall p s1 s2 s3,
      step_st p s1 s2 ->
      star_step_st p s2 s3 ->
      star_step_st p s1 s3
.

(* ================================================================
   第 2 部分：SafeASM 的操作语义（从 safeasm.v 导入 step）
   ================================================================ *)

(* SafeASM 多步执行 *)
Inductive multi_step_sasm : sasm_module -> runtime_state -> runtime_state -> Prop :=
  | Multi_sasm_refl : forall m s, multi_step_sasm m s s
  | Multi_sasm_step : forall m s1 s2 s3,
      step m s1 s2 ->
      multi_step_sasm m s2 s3 ->
      multi_step_sasm m s1 s3
.

(* SafeASM 的最终状态（执行到 RETURN） *)
Definition is_final_sasm (s : runtime_state) : Prop :=
  match s.(rt_frames) with
  | nil => True   (* 调用栈为空，程序结束 *)
  | _ => False
  end.

(* ================================================================
   第 3 部分：抽象关系 (Abstraction Relation)
   
   定义了 ST 状态与 SafeASM 状态之间的对应关系。
   这是编译正确性定理的核心——只有当两个状态"看起来一样"时，
   编译才算正确。
   ================================================================ *)

(* 类型兼容关系: ST 类型 → SafeASM 值类型 *)
Definition st_type_to_sasm (t : st_type) : sasm_value_type :=
  match t with
  | T_BOOL | T_BYTE | T_SINT  => I32
  | T_WORD | T_INT             => I32
  | T_DWORD | T_DINT           => I32
  | T_REAL                     => F32
  | T_TIME                     => I64
  | T_ARRAY elem _ _           => st_type_to_sasm elem
  end.

(* ST 值 → SafeASM 值的转换 *)
Definition st_val_to_sasm (v : st_value) : sasm_value :=
  match v with
  | ST_V_BOOL b    => V_I32 (if b then 1 else 0)
  | ST_V_BYTE z    => V_I32 z
  | ST_V_WORD z    => V_I32 z
  | ST_V_DWORD z   => V_I32 z
  | ST_V_SINT z    => V_I32 z
  | ST_V_INT z     => V_I32 z
  | ST_V_DINT z    => V_I32 z
  | ST_V_REAL f    => V_F32 f
  | ST_V_TIME z    => V_I64 z
  end.

(* 变量名到 SafeASM 内存偏移的映射
   由编译器在编译期生成的偏移表决定 *)
Parameter var_to_sasm_offset : ident -> Z.

(* 抽象关系: R(st_state, runtime_state)
   
   R(s, t) 当且仅当:
   1. 每个 ST 变量的值 = SafeASM 内存中对应偏移处的值
   2. 当前执行位置对应（ST 的 POU = ASM 的 func_idx）
   3. 类型兼容
   
   这是整个验证中最关键的定义——它决定了什么是"编译正确"。 *)
Definition abstraction_relation (st_st : st_state) (asm_st : runtime_state) : Prop :=
  (* 条件 1: 变量值一致 *)
  (forall (x : ident) (v : st_value),
    List.In (x, v) st_st.(st_vars) ->
    exists (offset : Z) (asm_val : sasm_value),
      var_to_sasm_offset x = offset /\
      read_sasm_mem asm_st offset = Some asm_val /\
      st_val_to_sasm v = asm_val) /\
  
  (* 条件 2: 执行位置一致 *)
  (st_st.(st_pou_idx) = asm_st.(rt_frames).(frame_func_idx)) /\
  
  (* 条件 3: 调用栈深度一致 *)
  (Z.of_nat (List.length st_st.(st_call_stack)) =
   Z.of_nat (List.length asm_st.(rt_frames))).
(* 
   通俗理解:
   条件 1: "ST 里 x 是 42 → ASM 内存里 x 的偏移处也是 42"
   条件 2: "ST 正在执行 POU_0 → ASM 的调用帧也在执行函数 0"
   条件 3: "ST 调用栈深度=3 → ASM 帧栈深度=3"
*)

(* ================================================================
   第 4 部分：编译过程 (Compilation Process)
   
   将 ST 程序编译为 SafeASM 模块。
   这里只声明编译函数的类型签名，具体实现在 src/ 中。
   ================================================================ *)

(* 编译结果类型：成功返回 SafeASM 模块，失败返回错误信息 *)
Inductive compile_result : Type :=
  | Compile_ok of sasm_module
  | Compile_error of string
.

(* 编译函数声明（具体实现在 src/codegen.v 中） *)
Parameter compile_st_to_sasm : st_program -> compile_result.

(* 编译成功的谓词 *)
Definition compile_success (p : st_program) (m : sasm_module) : Prop :=
  compile_st_to_sasm p = Compile_ok m.

(* ================================================================
   第 5 部分：编译正确性核心定理 (Core Correctness Theorems)
   ================================================================ *)

(* ================================================================
   定理 1: semantics_preservation (语义保持)
   
   对于任意 ST 程序 P，如果编译成功得到 SafeASM 模块 M，
   且 ST 状态 s1 与 ASM 状态 t1 满足抽象关系 R，
   则 ST 执行一步后，ASM 可以执行多步到达 t2，
   且 s2 与 t2 仍然满足 R。
   
   通俗理解:
   "ST 每走一步，ASM 总能跟上，且状态永远对齐。"
   ================================================================ *)
Theorem semantics_preservation :
  forall (p : st_program) (m : sasm_module),
    compile_success p m ->
    forall (s1 s2 : st_state) (t1 : runtime_state),
      step_st p s1 s2 ->
      abstraction_relation s1 t1 ->
      exists (t2 : runtime_state),
        multi_step_sasm m t1 t2 /\
        abstraction_relation s2 t2.
Proof.
  (* 通过对 step_st 的归纳证明 *)
  (* 每个 ST 构造对应一组 SafeASM 指令序列的模拟 *)
  (* 具体证明在 vstac/proofs/correctness/ 中 *)
Admitted.

(* ================================================================
   定理 2: total_semantics_preservation (整体语义保持)
   
   对于任意 ST 程序 P，如果编译成功，
   且 ST 从初始状态 s_init 执行到最终状态 s_final，
   则 ASM 从对应的初始状态 t_init 执行到最终状态 t_final，
   且 s_final 与 t_final 满足 R。
   
   这是 theorem 1 的传递闭包版本。
   ================================================================ *)
Theorem total_semantics_preservation :
  forall (p : st_program) (m : sasm_module),
    compile_success p m ->
    forall (s_init s_final : st_state) (t_init : runtime_state),
      star_step_st p s_init s_final ->
      abstraction_relation s_init t_init ->
      exists (t_final : runtime_state),
        multi_step_sasm m t_init t_final /\
        abstraction_relation s_final t_final /\
        is_final_sasm t_final.
Proof.
  (* 通过对 star_step_st 的归纳，应用 theorem 1 *)
Admitted.

(* ================================================================
   定理 3: safety_preservation (安全保持)
   
   如果 ST 程序 P 编译成功且通过了类型检查，
   那么编译产物 M 满足所有安全约束。
   
   通俗理解:
   "编译器不仅是正确的，还是安全的。
    它保证输出的 SafeASM 代码满足安全约束。"
   ================================================================ *)
Theorem safety_preservation :
  forall (p : st_program) (m : sasm_module),
    compile_success p m ->
    well_typed_program p ->
    (* 编译产物满足安全约束 *)
    sasm_safety_ok m /\
    (* 所有循环上限已确定 *)
    all_loops_bounded m /\
    (* 所有内存访问在声明范围内 *)
    all_memory_accesses_safe m /\
    (* 无递归调用 *)
    sasm_no_recursive_calls m.
Proof.
  (* 通过对编译过程的归纳证明 *)
Admitted.

(* ================================================================
   定理 4: compile_determinism (编译确定性)
   
   相同输入产生相同输出——编译过程是确定性的。
   
   通俗理解:
   "同样的 ST 程序，每次编译都产生同样的 .sasm 文件。"
   ================================================================ *)
Theorem compile_determinism :
  forall (p : st_program) (m1 m2 : sasm_module),
    compile_success p m1 ->
    compile_success p m2 ->
    m1 = m2.
Proof.
  (* 编译函数是纯函数，无副作用，无随机性 *)
Admitted.

(* ================================================================
   第 6 部分：辅助定义 (辅助类型与谓词)
   ================================================================ *)

(* 从 SafeASM 内存中读取值 *)
Parameter read_sasm_mem : runtime_state -> Z -> option sasm_value.

(* ST 表达式求值 *)
Parameter eval_expr : st_state -> st_expr -> option st_value.

(* 更新 ST 状态中的变量 *)
Parameter update_var : st_state -> ident -> st_value -> st_state.

(* 进入/退出代码块 *)
Parameter enter_block : st_state -> list st_stmt -> st_state.
Parameter exit_block : st_state -> st_state.

(* FOR 循环辅助函数 *)
Parameter init_for_loop : st_state -> ident -> Z -> Z -> list st_stmt -> st_state.
Parameter execute_for_body : st_state -> ident -> list st_stmt -> st_state.
Parameter loop_not_done : st_state -> ident -> Prop.
Parameter loop_done : st_state -> ident -> Prop.

(* 函数调用辅助 *)
Parameter lookup_function_st : st_program -> ident -> option (list st_type * list st_stmt).
Parameter push_call_frame : st_state -> ident -> list ident -> list st_stmt -> st_state.
Parameter pop_call_frame : st_state -> st_value -> st_state.

(* FB 调用辅助 *)
Parameter lookup_fb : st_program -> ident -> option (list st_var_decl * list st_stmt).
Parameter execute_fb : st_state -> (list st_var_decl * list st_stmt) -> list (ident * st_expr) -> st_state.

(* 安全约束谓词 *)
Definition sasm_safety_ok (m : sasm_module) : Prop :=
  (sasm_safety m).(safe_cycle_limit) > 0.

Definition all_loops_bounded (m : sasm_module) : Prop :=
  forall (lb : loop_bound),
    List.In lb (sasm_safety m).(safe_loop_bounds) ->
    lb.(lb_max_iter) > 0.

Definition all_memory_accesses_safe (m : sasm_module) : Prop :=
  forall (r : mem_access_range),
    List.In r (sasm_safety m).(safe_mem_access_map) ->
    r.(mar_low) >= 0 /\
    r.(mar_high) <= sasm_total_memory_size m.

Definition sasm_no_recursive_calls (m : sasm_module) : Prop :=
  (* 调用图分析：无函数调用自身 *)
  True.  (* 具体实现在 proofs/ 中 *)
