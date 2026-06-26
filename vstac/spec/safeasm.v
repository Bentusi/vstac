(* ================================================================
   vstac/spec/safeasm.v
   SafeASM — 安全汇编字节码 Coq 形式化定义
   
   本文件是 spec/safeasm-spec.md 的 Coq 形式化镜像。
   所有定义与文档保持同步。
   编码方式：固定宽度编码（非 LEB128）
   ================================================================ *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Local Open Scope Z_scope.
Require Import Stdlib.Floats.Floats.
Require Import Stdlib.Strings.String.
Import ListNotations.

(* ================================================================
   第 1 部分：值类型 (Value Types)
   ================================================================ *)

Inductive sasm_value_type : Type :=
  | I32           (* 32 位有符号整数 *)
  | I64           (* 64 位有符号整数 *)
  | F32           (* 32 位 IEEE 754 单精度浮点 *)
  | F64           (* 64 位 IEEE 754 双精度浮点 *)
.

(* 值类型的字节宽度 *)
Definition sasm_type_width (t : sasm_value_type) : Z :=
  match t with
  | I32 => 4
  | I64 => 8
  | F32 => 4
  | F64 => 8
  end.

(* 运行时值 *)
Inductive sasm_value : Type :=
  | V_I32 : Z -> sasm_value
  | V_I64 : Z -> sasm_value
  | V_F32 : float -> sasm_value
  | V_F64 : float -> sasm_value
.

(* 获取值的类型 *)
Definition value_type (v : sasm_value) : sasm_value_type :=
  match v with
  | V_I32 _ => I32
  | V_I64 _ => I64
  | V_F32 _ => F32
  | V_F64 _ => F64
  end.

(* ================================================================
   第 2 部分：内存参数 (Memory Arg)
   ================================================================ *)

Record memory_arg : Type := {
  mem_align  : Z;     (* 对齐要求 (log2) *)
  mem_offset : Z;     (* 基址偏移 *)
}.

(* ================================================================
   第 3 部分：安全断言 (Safety Assertion)
   ================================================================ *)

Inductive safety_assertion : Type :=
  | ASSERT_CYCLE_LIMIT : Z -> safety_assertion          (* 周期指令数上限 *)
  | ASSERT_STACK_DEPTH : Z -> safety_assertion          (* 栈深度上限 *)
  | ASSERT_MEM_BOUNDS : Z -> Z -> safety_assertion       (* 内存访问范围 [low, high) *)
.

(* ================================================================
   第 4 部分：指令集 (Instruction Set)
   ================================================================ *)

Inductive sasm_instr : Type :=
  (* --- 控制流 (0x00-0x06) --- *)
  | UNREACHABLE                      (* 不可达指令 *)
  | NOP                              (* 空操作 *)
  | BLOCK : Z -> sasm_instr          (* 块开始，参数=块内指令字节数 *)
  | LOOP : Z -> sasm_instr           (* 循环块开始 *)
  | BR : Z -> sasm_instr             (* 无条件跳转，参数=跳出深度 *)
  | BR_IF : Z -> sasm_instr          (* 条件跳转 *)
  | RETURN                           (* 函数返回 *)
  
  (* --- 函数调用 (0x10) --- *)
  | CALL : Z -> sasm_instr           (* 直接调用，参数=函数索引 *)
  
  (* --- 栈操作 (0x1A-0x22) --- *)
  | DROP                              (* 丢弃栈顶 *)
  | SELECT                            (* 三目选择 *)
  | LOCAL_GET : Z -> sasm_instr       (* 读取局部变量 *)
  | LOCAL_SET : Z -> sasm_instr       (* 写入局部变量 *)
  | LOCAL_TEE : Z -> sasm_instr       (* 写入并保留值 *)
  
  (* --- i32 常量 (0x41) --- *)
  | I32_CONST : Z -> sasm_instr       (* i32 常量 *)
  
  (* --- i32 比较 (0x45-0x4B) --- *)
  | I32_EQZ
  | I32_EQ | I32_NE
  | I32_LT_S | I32_LE_S | I32_GT_S | I32_GE_S
  
  (* --- i32 算术 (0x6A-0x6F) --- *)
  | I32_ADD | I32_SUB | I32_MUL
  | I32_DIV_S | I32_REM_S
  
  (* --- i32 位运算 (0x71-0x77) --- *)
  | I32_AND | I32_OR | I32_XOR
  | I32_SHL | I32_SHR_S
  | I32_ROTL | I32_ROTR
  
  (* --- i64 常量/比较/算术 (0x50-0x5B, 0x7C-0x80) --- *)
  | I64_CONST : Z -> sasm_instr
  | I64_EQZ
  | I64_EQ | I64_NE
  | I64_LT_S | I64_LE_S | I64_GT_S | I64_GE_S
  | I64_ADD | I64_SUB | I64_MUL
  | I64_DIV_S | I64_REM_S
  | I64_AND | I64_OR | I64_XOR
  | I64_SHL | I64_SHR_S
  
  (* --- 浮点常量 (0x43-0x44) --- *)
  | F32_CONST : float -> sasm_instr
  | F64_CONST : float -> sasm_instr
  
  (* --- f32 算术 (0x92-0xA2) --- *)
  | F32_ADD | F32_SUB | F32_MUL | F32_DIV
  | F32_EQ | F32_NE | F32_LT | F32_LE | F32_GT | F32_GE
  | F32_ABS | F32_NEG | F32_SQRT
  
  (* --- f64 算术 (0xA3-0xAF) --- *)
  | F64_ADD | F64_SUB | F64_MUL | F64_DIV
  | F64_EQ | F64_NE | F64_LT | F64_LE | F64_GT | F64_GE
  | F64_ABS | F64_NEG | F64_SQRT
  
  (* --- 类型转换 (0xA7-0xBB) --- *)
  | I32_WRAP_I64
  | I64_EXTEND_I32_S
  | I32_TRUNC_F32_S | I32_TRUNC_F64_S
  | F32_CONVERT_I32_S | F64_CONVERT_I32_S
  
  (* --- 内存操作 (0x28-0x39) --- *)
  | I32_LOAD : memory_arg -> sasm_instr
  | I64_LOAD : memory_arg -> sasm_instr
  | F32_LOAD : memory_arg -> sasm_instr
  | F64_LOAD : memory_arg -> sasm_instr
  | I32_STORE : memory_arg -> sasm_instr
  | I64_STORE : memory_arg -> sasm_instr
  | F32_STORE : memory_arg -> sasm_instr
  | F64_STORE : memory_arg -> sasm_instr
  
  (* --- 安全扩展 (0xFC-0xFD) --- *)
  | SAFE_ASSERT : safety_assertion -> sasm_instr
  | SAFE_BOUNDS_CHECK : Z -> Z -> sasm_instr   (* low, high *)
.

(* ================================================================
   第 5 部分：函数类型与函数定义
   ================================================================ *)

Record sasm_func_type : Type := {
  sasm_param_types  : list sasm_value_type;
  sasm_return_types : list sasm_value_type;   (* 0 或 1 个返回值 *)
}.

Record sasm_function : Type := {
  sasm_func_type_idx : Z;          (* 函数类型索引 *)
  sasm_locals         : list sasm_value_type;   (* 局部变量类型列表 *)
  sasm_body           : list sasm_instr;        (* 指令序列 *)
  sasm_stack_depth    : Z;                      (* 栈深度上限 *)
  sasm_cycle_budget   : Z;                      (* WCET 预算 *)
}.

(* ================================================================
   第 6 部分：内存段 (Memory Segments)
   ================================================================ *)

Inductive segment_type : Type :=
  | SEG_IO_INPUT          (* I/O 输入区，只读 *)
  | SEG_IO_OUTPUT         (* I/O 输出区，可写 *)
  | SEG_GLOBAL            (* 全局变量区 *)
  | SEG_FB_DATA           (* FB 实例数据区 *)
  | SEG_STACK             (* 栈区 *)
  | SEG_CONST             (* 常量区 *)
.

Record memory_segment : Type := {
  seg_type       : segment_type;
  seg_start      : Z;      (* 基址偏移 *)
  seg_size       : Z;      (* 段大小 *)
}.

(* ================================================================
   第 7 部分：I/O 映射条目
   ================================================================ *)

Inductive io_direction : Type :=
  | IO_INPUT | IO_OUTPUT.

Inductive io_type : Type :=
  | IO_AI | IO_AO | IO_DI | IO_DO.

Record io_entry_sasm : Type := {
  io_var_name   : string;     (* ST 变量名 *)
  io_mem_offset : Z;          (* SafeASM 内存偏移 *)
  io_channel_id : Z;          (* 物理通道 ID *)
  io_dir        : io_direction;
  io_type_kind  : io_type;
  io_bit_width  : Z;
  io_scale      : float;      (* 工程量转换系数 *)
  io_bias       : float;      (* 偏移量 *)
  io_safety_low : Z;          (* 安全下限 *)
  io_safety_high : Z;         (* 安全上限 *)
}.

(* ================================================================
   第 8 部分：安全注解 (Safety Annotation)
   ================================================================ *)

Record loop_bound : Type := {
  lb_func_idx     : Z;    (* 函数索引 *)
  lb_instr_offset : Z;    (* 循环指令偏移 *)
  lb_max_iter     : Z;    (* 最大迭代次数 *)
}.

Record mem_access_range : Type := {
  mar_low  : Z;
  mar_high : Z;
}.

Record safety_annotation : Type := {
  safe_level          : Z;                    (* 安全等级 *)
  safe_cycle_limit    : Z;                    (* 每周期最大指令数 *)
  safe_stack_depth    : Z;                    (* 全局栈深度上限 *)
  safe_loop_bounds    : list loop_bound;       (* 循环上限表 *)
  safe_mem_access_map : list mem_access_range; (* 合法内存访问范围 *)
}.

(* ================================================================
   第 9 部分：WCET 信息
   ================================================================ *)

Record wcet_func_info : Type := {
  wcet_func_idx  : Z;
  wcet_cycles    : Z;    (* 最差执行周期数 *)
  wcet_ns        : Z;    (* 最差执行时间 (ns) *)
}.

Record wcet_data : Type := {
  wcet_funcs : list wcet_func_info;
}.

(* ================================================================
   第 10 部分：完整 SafeASM 模块
   ================================================================ *)

Record sasm_module : Type := {
  (* 文件头 *)
  sasm_magic    : string;         (* "SASM" *)
  sasm_version  : Z;              (* 1 *)
  sasm_flags    : Z;              (* 特性位图 *)

  (* 核心数据 *)
  sasm_types      : list sasm_func_type;
  sasm_functions  : list sasm_function;
  sasm_memory_segments : list memory_segment;
  sasm_total_memory_size : Z;     (* 线性内存总大小 *)
  sasm_io_map     : list io_entry_sasm;
  
  (* 安全元数据 *)
  sasm_safety     : safety_annotation;
  sasm_wcet       : option wcet_data;
  
  (* 入口 *)
  sasm_entry_function : Z;        (* 入口函数索引 *)
}.

(* ================================================================
   第 11 部分：运行时状态 (Runtime State)
   ================================================================ *)

(* 值栈与帧栈 *)
Definition value_stack : Type := list sasm_value.

Record sasm_frame : Type := {
  frame_locals   : list sasm_value;   (* 局部变量 *)
  frame_func_idx : Z;                  (* 当前函数索引 *)
  frame_pc       : Z;                  (* 程序计数器 *)
}.

Definition frame_stack : Type := list sasm_frame.

(* 线性内存 = 字节列表 *)
Definition linear_memory : Type := list Z.  (* 每个 byte 为 0..255 的 Z *)

(* 完整运行时状态 *)
Record runtime_state : Type := {
  rt_values     : value_stack;       (* 值栈 *)
  rt_frames     : frame_stack;       (* 调用帧栈 *)
  rt_memory     : linear_memory;     (* 线性内存 *)
  rt_cycle_cnt  : Z;                 (* 当前周期指令计数 *)
}.

(* ================================================================
   第 12 部分：小步操作语义 (Small-step Semantics)
   ================================================================ *)

(* 辅助函数：执行二元 i32 运算 *)
Definition i32_bin_op (op : sasm_instr) (v1 v2 : Z) : option Z :=
  match op with
  | I32_ADD => Some (v1 + v2)
  | I32_SUB => Some (v1 - v2)
  | I32_MUL => Some (v1 * v2)
  | I32_DIV_S => if v2 =? 0 then None else Some (v1 / v2)
  | I32_REM_S => if v2 =? 0 then None else Some (Z.rem v1 v2)
  | I32_AND => Some (Z.land v1 v2)
  | I32_OR  => Some (Z.lor v1 v2)
  | I32_XOR => Some (Z.lxor v1 v2)
  | I32_SHL => Some (Z.shiftl v1 v2)
  | I32_SHR_S => Some (Z.shiftr v1 v2)
  | _ => None
  end.

(* ================================================================
   第 12b 部分：小步语义辅助函数 (Semantics Helpers)
   ================================================================ *)

(* 向值栈压入值 *)
Definition push_value (v : sasm_value) (s : runtime_state) : runtime_state :=
  {| rt_values := v :: s.(rt_values);
     rt_frames := s.(rt_frames);
     rt_memory := s.(rt_memory);
     rt_cycle_cnt := s.(rt_cycle_cnt) + 1;
  |}.

(* 弹出栈顶值 *)
Definition pop1 (s : runtime_state) : runtime_state :=
  match s.(rt_values) with
  | nil => s
  | _ :: vs => {| rt_values := vs; rt_frames := s.(rt_frames);
                  rt_memory := s.(rt_memory); rt_cycle_cnt := s.(rt_cycle_cnt) + 1; |}
  end.

(* 弹出两个栈顶值 *)
Definition pop2 (s : runtime_state) : runtime_state :=
  pop1 (pop1 s).

(* 替换栈顶值 *)
Definition state_with_top (v : sasm_value) (s : runtime_state) : runtime_state :=
  match s.(rt_values) with
  | nil => s
  | _ :: vs => {| rt_values := v :: vs; rt_frames := s.(rt_frames);
                  rt_memory := s.(rt_memory); rt_cycle_cnt := s.(rt_cycle_cnt); |}
  end.

(* 替换栈顶两个值 *)
Definition state_with_top2 (v1 v2 : sasm_value) (s : runtime_state) : runtime_state :=
  state_with_top v2 (state_with_top v1 s).

(* 检查内存地址是否有效（bool 版本，用于 step 定义） *)
Definition valid_address_bool (m : sasm_module) (addr offset : Z) : bool :=
  (0 <=? addr + offset) && (addr + offset <? m.(sasm_total_memory_size)).

(* 从内存读取值（简化实现） *)
Definition read_memory (s : runtime_state) (addr offset : Z) : option sasm_value :=
  Some (V_I32 0).

(* 存储值到内存（简化实现） *)
Definition state_after_store (addr offset : Z) (v : sasm_value) (s : runtime_state) : runtime_state :=
  s.

(* 跳转（简化占位） *)
Definition branch_to (depth : Z) (s : runtime_state) : runtime_state :=
  s.

(* 查找函数（简化占位） *)
Definition lookup_function (m : sasm_module) (idx : Z) : option (list sasm_value) :=
  None.

(* 创建新帧（简化占位） *)
Definition push_frame (idx : Z) (args : list sasm_value) (s : runtime_state) : runtime_state :=
  s.

(* 返回并恢复帧（简化占位） *)
Definition pop_frame_with_return (ret_val : sasm_value) (s : runtime_state) : runtime_state :=
  s.

(* 小步语义: step m s s' 表示从状态 s 执行一步到 s' *)
Inductive step : sasm_module -> runtime_state -> runtime_state -> Prop :=
  | Step_const : forall m s v,
      step m s (push_value (V_I32 v) s)
  
  | Step_i32_add : forall m s v1 v2 new_v,
      Some new_v = i32_bin_op I32_ADD v1 v2 ->
      step m
        (state_with_top2 (V_I32 v1) (V_I32 v2) s)
        (state_with_top (V_I32 new_v) (pop2 s))
  
    (* 安全断言: 运行时检查 *)
  | Step_safe_assert_cycle : forall m s limit,
      Z.lt s.(rt_cycle_cnt) limit ->
      step m s s
.

(* 多步执行 *)
Inductive multi_step : sasm_module -> runtime_state -> runtime_state -> Prop :=
  | Multi_refl : forall m s, multi_step m s s
  | Multi_step : forall m s1 s2 s3,
      step m s1 s2 ->
      multi_step m s2 s3 ->
      multi_step m s1 s3
.

(* ================================================================
   第 13 部分：安全执行 (Safe Execution)
   ================================================================ *)

(* 地址有效性检查 *)
Definition valid_address (m : sasm_module) (addr : Z) (offset : Z) : Prop :=
  0 <= addr + offset < sasm_total_memory_size m.

(* 安全步进: 每一步都需满足安全约束 *)
(* 所有内存访问在声明范围内 *)
Definition all_memory_accesses_valid (m : sasm_module) (s : runtime_state) : Prop :=
  forall (r : mem_access_range),
    In r (sasm_safety m).(safe_mem_access_map) ->
    valid_address m r.(mar_low) r.(mar_high).

Inductive safe_step : sasm_module -> runtime_state -> runtime_state -> Prop :=
  | SafeStep : forall m s s',
      step m s s' ->
      (* 周期指令数上限 *)
      s.(rt_cycle_cnt) < (sasm_safety m).(safe_cycle_limit) ->
      (* 栈深度上限 *)
      Z.of_nat (List.length s.(rt_frames)) <= (sasm_safety m).(safe_stack_depth) ->
      (* 所有内存访问合法 *)
      all_memory_accesses_valid m s ->
      safe_step m s s'.

(* ================================================================
   第 14 部分：编码/解码可逆性定理
   ================================================================ *)

(* 类型安全定理声明（后续在 proofs/ 中实现） *)
(* Theorem sasm_type_safety : ... *)
