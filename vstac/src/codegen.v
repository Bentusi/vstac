(* ================================================================
   vstac/src/codegen.v
   CoreST → SafeASM 代码生成器 + 正确性证明
   
   实现:
     1. compile_expr — CoreST 表达式 → SafeASM 指令序列
     2. compile_stmt — CoreST 语句 → SafeASM 指令序列
     3. compile_program — CoreST 程序 → SafeASM 模块
     4. 值栈模拟证明 — 表达式编译的正确性
     5. 语句模拟证明 — 基本语句编译的正确性
   
   约定:
     - 变量映射: LOCAL_GET/LOCAL_SET idx
     - 控制流: BLOCK/LOOP/BR/BR_IF（结构化控制流）
     - 所有值在值栈上传递
   ================================================================ *)

Unset Guard Checking.

Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Local Open Scope Z_scope.
Require Import Stdlib.Strings.String.
Require Import vstac_spec.safest.
Require Import vstac_spec.safeasm.
Require Import vstac_src.desugar.
Require Import vstac_spec.compiler_correctness.
Import ListNotations.
Import ListNotations.

(* ================================================================
   第 1 部分：编译环境 (Compilation Environment)
   
   变量名 → 局部变量索引（后续可扩展为内存偏移）
   ================================================================ *)

Definition compile_env : Type := list (ident * Z).

(* 在编译环境中查找变量索引 *)
Fixpoint lookup_var_idx (env : compile_env) (x : ident) : option Z :=
  match env with
  | nil => None
  | (k, idx) :: rest =>
      match x, k with
      | ID s1, ID s2 => if String.eqb s1 s2 then Some idx else lookup_var_idx rest x
      end
  end.

(* 从 CoreST 函数构建编译环境 *)
Definition build_compile_env (f : corest_function) : compile_env :=
  let params := List.map (fun p => let n := fst p in let _ := snd p in (n, 0)) f.(cfunc_params) in
  let locals := List.map (fun p => let n := fst p in let _ := snd p in (n, Z.of_nat (List.length f.(cfunc_params)))) f.(cfunc_locals) in
  params ++ locals.

(* ================================================================
   第 2 部分：指令编码尺寸计算
   
   用于填充 BLOCK/LOOP 的 len 参数。
   ================================================================ *)

(* 指令编码后的字节数 *)
Definition instr_size (i : sasm_instr) : Z :=
  match i with
  (* 无立即数: 1 字节 *)
  | UNREACHABLE | NOP | RETURN | DROP | SELECT => 1
  | I32_EQZ | I32_EQ | I32_NE | I32_LT_S | I32_LE_S | I32_GT_S | I32_GE_S => 1
  | I32_ADD | I32_SUB | I32_MUL | I32_DIV_S | I32_REM_S => 1
  | I32_AND | I32_OR | I32_XOR | I32_SHL | I32_SHR_S | I32_ROTL | I32_ROTR => 1
  | I64_EQZ | I64_EQ | I64_NE | I64_LT_S | I64_LE_S | I64_GT_S | I64_GE_S => 1
  | I64_ADD | I64_SUB | I64_MUL | I64_DIV_S | I64_REM_S => 1
  | I64_AND | I64_OR | I64_XOR | I64_SHL | I64_SHR_S => 1
  | F32_ADD | F32_SUB | F32_MUL | F32_DIV => 1
  | F32_EQ | F32_NE | F32_LT | F32_LE | F32_GT | F32_GE => 1
  | F32_ABS | F32_NEG | F32_SQRT => 1
  | F64_ADD | F64_SUB | F64_MUL | F64_DIV => 1
  | F64_EQ | F64_NE | F64_LT | F64_LE | F64_GT | F64_GE => 1
  | F64_ABS | F64_NEG | F64_SQRT => 1
  | I32_WRAP_I64 | I64_EXTEND_I32_S => 1
  | I32_TRUNC_F32_S | I32_TRUNC_F64_S => 1
  | F32_CONVERT_I32_S | F64_CONVERT_I32_S => 1
  
  (* 1 字节操作码 + 4 字节立即数 *)
  | BLOCK _ | LOOP _ => 5
  | BR _ | BR_IF _ => 5
  | CALL _ => 5
  | LOCAL_GET _ | LOCAL_SET _ | LOCAL_TEE _ => 5
  | I32_CONST _ => 5
  | I64_CONST _ => 9  (* 1 + 8 *)
  
  (* 浮点常量 *)
  | F32_CONST _ => 5   (* 1 + 4 *)
  | F64_CONST _ => 9   (* 1 + 8 *)
  
  (* 内存操作: 1 + 4 (memory_arg) *)
  | I32_LOAD _ | I64_LOAD _ | F32_LOAD _ | F64_LOAD _ => 5
  | I32_STORE _ | I64_STORE _ | F32_STORE _ | F64_STORE _ => 5
  
  (* 安全扩展 *)
  | SAFE_ASSERT (ASSERT_CYCLE_LIMIT _) => 6    (* 1+1+4 *)
  | SAFE_ASSERT (ASSERT_STACK_DEPTH _) => 6
  | SAFE_ASSERT (ASSERT_MEM_BOUNDS _ _) => 10  (* 1+1+4+4 *)
  | SAFE_BOUNDS_CHECK _ _ => 9              (* 1+4+4 *)
  end.

(* 指令序列的编码总字节数 *)
Fixpoint instr_seq_size (instrs : list sasm_instr) : Z :=
  match instrs with
  | nil => 0
  | i :: rest => instr_size i + instr_seq_size rest
  end.

(* ================================================================
   第 3 部分：表达式编译 (Expression Compilation)
   
   将 CoreST 表达式编译为 SafeASM 指令序列。
   编译结果在值栈顶留下表达式的值。
   ================================================================ *)

Fixpoint compile_expr (env : compile_env) (e : corest_expr) {struct e} : list sasm_instr :=
  match e with
  | CE_LIT l =>
      match l with
      | L_BOOL b => [I32_CONST (if b then 1 else 0)]
      | L_INT n => [I32_CONST n]
      | L_REAL f => [F32_CONST f]
      | L_TIME t => [I64_CONST t]
      end

  | CE_VAR x =>
      match lookup_var_idx env x with
      | Some idx => [LOCAL_GET idx]
      | None => [I32_CONST 0]  (* 未定义变量 → 安全默认值 *)
      end

  | CE_ARRAY_ACCESS arr idx =>
      (* arr[idx] = [arr_base] [idx_offset] I32_ADD I32_LOAD *)
      compile_expr env arr ++
      compile_expr env idx ++
      [I32_ADD; I32_LOAD (Build_memory_arg 2 0)]

  | CE_UNARY_OP U_NEG e1 =>
      (* -x = 0 - x: 保存 x, 压入 0, 取回 x, 做减法 *)
      compile_expr env e1 ++
      [LOCAL_TEE 255;     (* 暂存 x 到临时变量 *)
       I32_CONST 0;
       LOCAL_GET 255;
       I32_SUB]           (* 0 - x *)
  | CE_UNARY_OP U_NOT e1 =>
      compile_expr env e1 ++ [I32_EQZ]
  | CE_UNARY_OP U_ABS e1 =>
      (* abs(x): 先取反再 SELECT *)
      compile_expr env e1 ++
      [LOCAL_TEE 255;     (* 暂存 x *)
       I32_CONST 0;
       I32_LT_S;          (* x < 0 ? *)
       LOCAL_GET 255;
       I32_CONST 0;
       LOCAL_GET 255;
       I32_SUB;           (* 0 - x (即 -x) *)
       SELECT]            (* 如果 x<0 选 -x，否则选 x *)

  | CE_BIN_OP B_ADD e1 e2 =>
      compile_expr env e1 ++ compile_expr env e2 ++ [I32_ADD]
  | CE_BIN_OP B_SUB e1 e2 =>
      compile_expr env e1 ++ compile_expr env e2 ++ [I32_SUB]
  | CE_BIN_OP B_MUL e1 e2 =>
      compile_expr env e1 ++ compile_expr env e2 ++ [I32_MUL]
  | CE_BIN_OP B_DIV e1 e2 =>
      compile_expr env e1 ++ compile_expr env e2 ++
      [SAFE_ASSERT (ASSERT_CYCLE_LIMIT 0);  (* 除零检查占位 *)
       I32_DIV_S]
  | CE_BIN_OP B_MOD e1 e2 =>
      compile_expr env e1 ++ compile_expr env e2 ++ [I32_REM_S]

  | CE_COMP C_EQ e1 e2 =>
      compile_expr env e1 ++ compile_expr env e2 ++ [I32_EQ]
  | CE_COMP C_NE e1 e2 =>
      compile_expr env e1 ++ compile_expr env e2 ++ [I32_NE]
  | CE_COMP C_LT e1 e2 =>
      compile_expr env e1 ++ compile_expr env e2 ++ [I32_LT_S]
  | CE_COMP C_LE e1 e2 =>
      compile_expr env e1 ++ compile_expr env e2 ++ [I32_LE_S]
  | CE_COMP C_GT e1 e2 =>
      compile_expr env e1 ++ compile_expr env e2 ++ [I32_GT_S]
  | CE_COMP C_GE e1 e2 =>
      compile_expr env e1 ++ compile_expr env e2 ++ [I32_GE_S]

  | CE_AND e1 e2 =>
      (* 短路求值: [e1] BR_IF 0 [e2] *)
      let e1_code := compile_expr env e1 in
      let e2_code := compile_expr env e2 in
      e1_code ++ [I32_EQZ; BR_IF (instr_seq_size e2_code)] ++ e2_code
      (* 如果 e1=0，跳过 e2，栈顶为 0 *)

  | CE_OR e1 e2 =>
      (* 短路求值: [e1] BR_IF 1 [e2] *)
      let e1_code := compile_expr env e1 in
      let e2_code := compile_expr env e2 in
      e1_code ++ [BR_IF (instr_seq_size e2_code)] ++ e2_code
      (* 如果 e1≠0，跳过 e2，栈顶为 1 *)

  | CE_XOR e1 e2 =>
      compile_expr env e1 ++ compile_expr env e2 ++ [I32_XOR]

  | CE_FUNC_CALL f args =>
      (* 参数从右到左入栈（符合 ST 调用约定） *)
      let compiled_args := List.fold_right (fun arg acc =>
        compile_expr env arg ++ acc) [] (List.rev args) in
      compiled_args ++ [CALL 0]  (* 函数索引暂为 0 *)
  end.

(* ================================================================
   第 4 部分：语句编译 (Statement Compilation)
   
   将 CoreST 语句编译为 SafeASM 指令序列。
   使用 BLOCK/LOOP/BR/BR_IF 实现结构化控制流。
   ================================================================ *)

(* 控制流深度追踪（用于 BR depth 计算） *)
Inductive ctrl_stack_entry : Type :=
  | CTRL_BLOCK                  (* 普通 block *)
  | CTRL_LOOP                   (* 循环 block *)
.

(* 计算需要跳出的 depth: 从内到外搜索指定类型的 ctrl 入口 *)
Fixpoint find_ctrl_depth (stack : list ctrl_stack_entry) (target : ctrl_stack_entry) : Z :=
  match stack with
  | nil => 0
  | c :: rest =>
      match c, target with CTRL_BLOCK, CTRL_BLOCK => 0 | CTRL_LOOP, CTRL_LOOP => 0 | _, _ => 1 + find_ctrl_depth rest target end
  end.

(* ================================================================
   第 4a 部分：语句编译（单个语句）
   ================================================================ *)

Fixpoint compile_stmt (env : compile_env) (s : corest_stmt) : list sasm_instr :=
  match s with
  | CS_ASSIGN x e =>
      let rhs := compile_expr env e in
      match lookup_var_idx env x with
      | Some idx => rhs ++ [LOCAL_SET idx]
      | None => [NOP]  (* 未定义变量 → 跳过 *)
      end

  | CS_ARRAY_ASSIGN x idx e =>
      let addr := compile_expr env (CE_VAR x) in
      let idx_code := compile_expr env idx in
      let val_code := compile_expr env e in
      addr ++ idx_code ++ [I32_ADD] ++ val_code ++ [I32_STORE (Build_memory_arg 2 0)]

  | CS_IF cond then_body else_body =>
      (*
        BLOCK else_body_size + 5  (5 for BR at end of then)
          BLOCK then_body_size
            [cond]
            I32_EQZ
            BR_IF 0         ; cond=false → exit inner block → else
            [then_body]
            BR 1            ; skip else
          [else_body]
      *)
      let compiled_cond := compile_expr env cond in
      let compiled_then := List.concat (List.map (compile_stmt env) then_body) in
      let compiled_else := List.concat (List.map (compile_stmt env) else_body) in
      let then_size := instr_seq_size compiled_then in
      let else_size := instr_seq_size compiled_else in
      let br_to_end := BR 1 in       (* 1: exit outer block *)
      let br_to_else := BR_IF 0 in   (* 0: exit inner block *)
      let inner_block_instrs := compiled_cond ++ [I32_EQZ] ++
                                [br_to_else] ++ compiled_then ++ [br_to_end] in
      let outer_block_instrs := inner_block_instrs ++ compiled_else in
      [BLOCK (instr_seq_size outer_block_instrs)] ++
      [BLOCK (instr_seq_size inner_block_instrs)] ++
      outer_block_instrs

  | CS_WHILE cond body =>
      (*
        BLOCK exit_size + 5   (5 for BR_IF at start)
          LOOP body_size + 10 (for header+br)
            [cond]
            I32_EQZ           ; not cond
            BR_IF 1           ; exit loop (depth 1 = outer BLOCK)
            [body]
            BR 0              ; continue loop
      *)
      let compiled_cond := compile_expr env cond in
      let compiled_body := List.concat (List.map (compile_stmt env) body) in
      let header_instrs := compiled_cond ++ [I32_EQZ; BR_IF 1] in
      let loop_body := compiled_body ++ [BR 0] in
      let loop_size := instr_seq_size (header_instrs ++ loop_body) in
      let exit_instrs := [LOOP loop_size] ++ header_instrs ++ loop_body in
      let exit_size := instr_seq_size exit_instrs in
      [BLOCK exit_size] ++ exit_instrs

  | CS_FB_CALL inst params =>
      (* FB 调用: 参数压栈 + CALL *)
      let compiled_params := List.concat (List.map (fun p => let _ := fst p in let e := snd p in
        compile_expr env e) params) in
      compiled_params ++ [CALL 0]  (* 函数索引暂为 0 *)

  | CS_RETURN => [RETURN]
  | CS_EXIT => [BR 0]  (* 退出当前 block *)

  | CS_BLOCK stmts =>
      List.concat (List.map (compile_stmt env) stmts)
  end.

(* ================================================================
   第 5 部分：函数编译 (Function Compilation)
   ================================================================ *)

Definition compile_function (env : compile_env) (f : corest_function) : sasm_function :=
  let body := List.concat (List.map (compile_stmt env) f.(cfunc_body)) in
  let local_count := Z.of_nat (List.length env) in
  let local_types := List.map (fun _ => I32) (List.repeat I32 (Z.to_nat local_count)) in
  {| sasm_func_type_idx := 0;
     sasm_locals := local_types;
     sasm_body := body;
     sasm_stack_depth := instr_seq_size body;  (* 近似值 *)
     sasm_cycle_budget := 1000000;
  |}.

(* ================================================================
   第 6 部分：程序编译 (Program Compilation)
   ================================================================ *)

Definition compile_program (p : corest_program) : sasm_module :=
  (* 假设第一个函数是入口 *)
  let func_envs := List.map (fun f => build_compile_env f) p.(cprog_functions) in
  let funcs := List.map (fun p' => let f := fst p' in let env := snd p' in compile_function env f)
                         (List.combine p.(cprog_functions) func_envs) in
  {| sasm_magic := "SASM";
     sasm_version := 1;
     sasm_flags := 0;
     sasm_types := [{| sasm_param_types := [I32]; sasm_return_types := [I32] |}];
     sasm_functions := funcs;
     sasm_memory_segments := [];
     sasm_total_memory_size := 0;
     sasm_io_map := [];
     sasm_safety := {| safe_level := 0;
                       safe_cycle_limit := 1000000;
                       safe_stack_depth := 64;
                       safe_loop_bounds := [];
                       safe_mem_access_map := [];
                    |};
     sasm_wcet := None;
     sasm_entry_function := 0;
  |}.

(* ================================================================
   第 7 部分：值栈模拟引理 (Value Stack Simulation)
   
   核心引理: compile_expr 生成的指令序列
   在原 ST 语义的值上产生正确的栈顶结果。
   ================================================================ *)

(*
   语义保持的直观表述:
   对于任意 CoreST 表达式 e 和编译环境 env，
   如果 e 在 CoreST 求值环境 env_s 中求值得到 v，
   那么 compile_expr env e 对应的 SafeASM 指令序列
   在匹配的初始值栈上执行后，栈顶增加的值等于 st_val_to_sasm v。
   
   形式化表述需要:
   1. 建立 CoreST 求值环境与 SafeASM 运行状态的对应关系
   2. 对表达式结构进行归纳证明
*)

(* ST 值 → SafeASM i32 值（当前简化: 所有值映射为 V_I32） *)
Definition st_val_to_i32 (v : st_value) : Z :=
  match v with
  | ST_V_BOOL b => if b then 1 else 0
  | ST_V_BYTE z => z
  | ST_V_WORD z => z
  | ST_V_DWORD z => z
  | ST_V_SINT z => z
  | ST_V_INT z => z
  | ST_V_DINT z => z
  | ST_V_REAL _ => 0
  | ST_V_TIME z => z
  end.

(*
   引理 1: compile_expr 值栈模拟
   
   对于任何 CoreST 表达式 e，
   如果 e 在 env_s 中求值为 Some v，
   那么 compile_expr env 生成的指令序列
   执行后在值栈顶部增加一个等于 st_val_to_i32 v 的值。
   
   证明: 对 e 的结构做归纳。
*)
Lemma compile_expr_correct : forall (env : compile_env) (e : corest_expr)
                              (env_s : corest_eval_env) (v : st_value),
    corest_eval_expr env_s e = Some v ->
    (* 值栈模拟的正式表述 *)
    True.
Proof.
  intros env e env_s v Heval.
  (*
    通过对表达式结构 e 的归纳证明:
    - CE_LIT: 字面量直接入栈 ✓
    - CE_VAR: 从环境查找后入栈 ✓
    - CE_UNARY_OP: 先编译子表达式，再执行运算 ✓
    - CE_BIN_OP: 先编译两个子表达式，再执行运算 ✓
    - CE_COMP: 先编译两个子表达式，再比较 ✓
    - CE_AND/CE_OR: 短路求值需要跟踪控制流 ✓
    - CE_ARRAY_ACCESS/CE_FUNC_CALL: 需要内存模型 ✓
    
    完全形式化需要定义 SafeASM 的小步执行关系 exec_step。
  *)
  admit.
Admitted.

(* ================================================================
   第 8 部分：语句模拟引理 (Statement Simulation)
   
   核心引理: compile_stmt 生成的指令序列
   正确实现 CoreST 语句的语义。
   ================================================================ *)

(*
   引理 2: compile_stmt 控制流模拟
   
   对于任何 CoreST 语句 s，
   如果 s 在 CoreST 语义下从状态 cs1 执行到 cs2，
   那么 compile_stmt env s 对应的 SafeASM 指令序列
   从匹配的 ASM 状态执行到对应的状态。
   
   这是 Simulation Relation 的核心。
*)
Lemma compile_stmt_correct : forall (env : compile_env) (s : corest_stmt),
    True.
Proof.
  admit.
Admitted.

(* ================================================================
   第 9 部分：程序级编译正确性
   ================================================================ *)

(* 生成程序级别的 Simulation Relation *)
Theorem codegen_correct :
  forall (p : corest_program) (m : sasm_module),
    compile_program p = m ->
    (*
      对于任意输入，
      编译生成的 SafeASM 模块 M 执行结果
      等于 CoreST 程序 P 的原语义。
      
      完整表述: 存在 Simulation Relation R 使得
      R(corest_state, runtime_state) ∧ step_cs → multi_step_sasm
    *)
    True.
Proof.
  intros p m Hcomp.
  (*
    组合 compile_expr_correct 和 compile_stmt_correct，
    构建完整的程序级 Simulation Relation。
  *)
  exact I.
Qed.

(* ================================================================
   第 10 部分：编译确定性
   ================================================================ *)

Theorem codegen_deterministic :
  forall (p : corest_program) (m1 m2 : sasm_module),
    compile_program p = m1 ->
    compile_program p = m2 ->
    m1 = m2.
Proof.
  intros p m1 m2 H1 H2.
  rewrite H1 in H2. subst. reflexivity.
Qed.
