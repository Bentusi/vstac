(* ================================================================
   vstac/spec/safest.v
   SafeST — IEC 61131-3 Structured Text 安全子集 Coq 形式化定义
   
   本文件是 spec/safest-spec.md 的 Coq 形式化镜像。
   所有定义与文档保持同步。
   ================================================================ *)

(* ================================================================
   第 1 部分：词法单元 (Tokens)
   ================================================================ *)

Inductive token : Type :=
  (* 关键字 *)
  | TK_PROGRAM | TK_FUNCTION | TK_FUNCTION_BLOCK
  | TK_END_PROGRAM | TK_END_FUNCTION | TK_END_FUNCTION_BLOCK
  | TK_IF | TK_THEN | TK_ELSIF | TK_ELSE | TK_END_IF
  | TK_CASE | TK_OF | TK_END_CASE
  | TK_FOR | TK_TO | TK_BY | TK_DO | TK_END_FOR
  | TK_WHILE | TK_END_WHILE
  | TK_REPEAT | TK_UNTIL | TK_END_REPEAT
  | TK_RETURN | TK_EXIT
  | TK_VAR | TK_VAR_INPUT | TK_VAR_OUTPUT | TK_VAR_IN_OUT
  | TK_VAR_GLOBAL | TK_END_VAR
  | TK_CONSTANT | TK_RETAIN
  | TK_TRUE | TK_FALSE
  | TK_AND | TK_OR | TK_XOR | TK_NOT
  | TK_MOD | TK_ABS
  (* 字面量 *)
  | TK_INT_LIT of Z              (* 整数常量 *)
  | TK_REAL_LIT of float         (* 浮点常量 *)
  | TK_TIME_LIT of Z             (* TIME 常量，纳秒 *)
  | TK_BOOL_LIT of bool          (* 布尔常量 *)
  (* 标识符 *)
  | TK_IDENT of string           (* 变量名/函数名/FB名 *)
  (* 运算符 *)
  | TK_PLUS | TK_MINUS | TK_STAR | TK_SLASH
  | TK_EQ | TK_NE | TK_LT | TK_LE | TK_GT | TK_GE
  | TK_ASSIGN                    (* := *)
  | TK_COLON | TK_SEMI | TK_COMMA | TK_DOT
  | TK_LPAREN | TK_RPAREN
  | TK_LBRACK | TK_RBRACK        (* 数组下标 [ ] *)
  | TK_RANGE                     (* .. *)
  (* 其他 *)
  | TK_EOF
.

(* ================================================================
   第 1b 部分：标识符类型
   ================================================================ *)

(* 标识符类型 *)
Inductive ident : Type :=
  | ID of string
.

(* 标识符相等性比较 *)
Definition ident_eq (x y : ident) : bool :=
  match x, y with
  | ID s1, ID s2 => String.eqb s1 s2
  end.

(* ================================================================
   第 2 部分：类型系统 (Type System)
   ================================================================ *)

Inductive st_type : Type :=
  | T_BOOL                       (* BOOL *)
  | T_BYTE                       (* BYTE *)
  | T_WORD                       (* WORD *)
  | T_DWORD                      (* DWORD *)
  | T_SINT                       (* SINT *)
  | T_INT                        (* INT *)
  | T_DINT                       (* DINT *)
  | T_REAL                       (* REAL *)
  | T_TIME                       (* TIME *)
  | T_ARRAY of st_type * Z * Z   (* 静态数组: 元素类型 × 下界 × 上界 *)
.

(* 类型的位宽（用于内存布局计算） *)
Definition type_width (t : st_type) : Z :=
  match t with
  | T_BOOL   => 1
  | T_BYTE   => 8
  | T_WORD   => 16
  | T_DWORD  => 32
  | T_SINT   => 8
  | T_INT    => 16
  | T_DINT   => 32
  | T_REAL   => 32
  | T_TIME   => 64
  | T_ARRAY elem low high => (high - low + 1) * type_width elem
  end.

(* 类型兼容性（隐式转换规则） *)
Inductive type_compatible : st_type -> st_type -> Prop :=
  | Comp_same : forall t, type_compatible t t
  (* 整数提升: SINT → INT → DINT *)
  | Comp_sint_int : type_compatible T_SINT T_INT
  | Comp_sint_dint : type_compatible T_SINT T_DINT
  | Comp_int_dint : type_compatible T_INT T_DINT
  (* 位串提升: BYTE → WORD → DWORD *)
  | Comp_byte_word : type_compatible T_BYTE T_WORD
  | Comp_byte_dword : type_compatible T_BYTE T_DWORD
  | Comp_word_dword : type_compatible T_WORD T_DWORD
.

(* 提升到公共类型 *)
Inductive promote_type : st_type -> st_type -> st_type -> Prop :=
  | Promote_same : forall t, promote_type t t t
  | Promote_sint_int : promote_type T_SINT T_INT T_INT
  | Promote_sint_dint : promote_type T_SINT T_DINT T_DINT
  | Promote_int_dint : promote_type T_INT T_DINT T_DINT
  | Promote_byte_word : promote_type T_BYTE T_WORD T_WORD
  | Promote_byte_dword : promote_type T_BYTE T_DWORD T_DWORD
  | Promote_word_dword : promote_type T_WORD T_DWORD T_DWORD
.

(* ================================================================
   第 3 部分：字面量 (Literals)
   ================================================================ *)

Inductive st_literal : Type :=
  | L_BOOL of bool
  | L_INT of Z                (* 整数字面量，范围对应具体类型 *)
  | L_REAL of float           (* 实数字面量 *)
  | L_TIME of Z               (* 时间字面量，单位纳秒 *)
.

(* 字面量的类型推断 *)
Definition literal_type (l : st_literal) : option st_type :=
  match l with
  | L_BOOL _ => Some T_BOOL
  | L_INT _  => Some T_DINT    (* 默认整数类型 *)
  | L_REAL _ => Some T_REAL
  | L_TIME _ => Some T_TIME
  end.

(* ================================================================
   第 4 部分：表达式 (Expressions)
   ================================================================ *)

Inductive unary_op : Type :=
  | U_NEG     (* 一元负号 - *)
  | U_NOT     (* 逻辑非 NOT *)
  | U_ABS     (* 绝对值 ABS *)
.

Inductive binary_op : Type :=
  | B_ADD     (* + *)
  | B_SUB     (* - *)
  | B_MUL     (* * *)
  | B_DIV     (* / *)
  | B_MOD     (* MOD *)
.

Inductive compare_op : Type :=
  | C_EQ      (* = *)
  | C_NE      (* <> *)
  | C_LT      (* < *)
  | C_LE      (* <= *)
  | C_GT      (* > *)
  | C_GE      (* >= *)
.

Inductive st_expr : Type :=
  | E_LIT of st_literal                            (* 字面量 *)
  | E_VAR of ident                                 (* 变量引用 *)
  | E_ARRAY_ACCESS of st_expr * st_expr             (* 数组索引 arr[idx] *)
  | E_UNARY_OP of unary_op * st_expr               (* 一元运算 *)
  | E_BIN_OP of binary_op * st_expr * st_expr       (* 二元运算 *)
  | E_COMP of compare_op * st_expr * st_expr        (* 比较运算 *)
  | E_AND of st_expr * st_expr                      (* 逻辑 AND（短路求值） *)
  | E_OR of st_expr * st_expr                       (* 逻辑 OR（短路求值） *)
  | E_XOR of st_expr * st_expr                      (* 逻辑 XOR *)
  | E_FUNC_CALL of ident * list st_expr             (* 函数调用 *)
.

(* ================================================================
   第 5 部分：语句 (Statements)
   ================================================================ *)

Inductive st_stmt : Type :=
  | S_ASSIGN of ident * st_expr                                (* x := e *)
  | S_ARRAY_ASSIGN of ident * st_expr * st_expr                 (* a[i] := e *)
  | S_IF of st_expr * list st_stmt * option (list st_stmt)      (* IF cond THEN stmts [ELSE stmts] *)
  | S_CASE of st_expr * list (case_element) * option (list st_stmt)
  | S_FOR of ident * st_expr * st_expr * option st_expr * list st_stmt
  | S_WHILE of st_expr * list st_stmt
  | S_REPEAT of list st_stmt * st_expr
  | S_FB_CALL of ident * list (ident * st_expr)                 (* FB_inst(param:=val, ...) *)
  | S_RETURN
  | S_EXIT
with case_element : Type :=
  | CASE_ELEM of list case_value * list st_stmt
with case_value : Type :=
  | CV_SINGLE of st_literal
  | CV_RANGE of st_literal * st_literal                          (* low..high *)
.

(* ================================================================
   第 6 部分：变量声明 (Variable Declarations)
   ================================================================ *)

Inductive var_direction : Type :=
  | D_INPUT
  | D_OUTPUT
  | D_IN_OUT
  | D_LOCAL
  | D_GLOBAL
.

Inductive var_qualifier : Type :=
  | Q_NONE
  | Q_CONSTANT
  | Q_RETAIN
.

Record st_var_decl : Type := {
  var_name    : ident;
  var_type    : st_type;
  var_dir     : var_direction;
  var_qual    : var_qualifier;
  var_init    : option st_literal;   (* 初始值 *)
}.



(* ================================================================
   第 7 部分：程序组织单元 (POU)
   ================================================================ *)

Inductive st_pou : Type :=
  | P_PROGRAM of {
      pou_name      : ident;
      pou_var_decls : list st_var_decl;
      pou_body      : list st_stmt;
    }
  | P_FUNCTION of {
      pou_name       : ident;
      pou_return_type : st_type;
      pou_var_decls  : list st_var_decl;
      pou_body       : list st_stmt;
    }
  | P_FUNCTION_BLOCK of {
      pou_name      : ident;
      pou_var_decls : list st_var_decl;
      pou_body      : list st_stmt;
    }
.

Record io_entry : Type := {
  io_var_name    : ident;         (* ST 变量名 *)
  io_channel_id  : Z;             (* 物理通道 ID *)
  io_direction   : var_direction; (* INPUT / OUTPUT *)
  io_type        : st_type;       (* 数据类型 *)
}.

(* ================================================================
   第 8 部分：完整程序 (Complete Program)
   ================================================================ *)

Record st_program : Type := {
  global_vars    : list st_var_decl;   (* 全局变量声明 *)
  pou_list       : list st_pou;        (* POU 定义列表 *)
  io_mapping     : list io_entry;      (* I/O 映射条目 *)
  entry_point    : ident;              (* 入口 PROGRAM 名称 *)
}.

(* ================================================================
   第 9 部分：类型检查规则 (Type Checking Rules)
   ================================================================ *)

(* 类型环境：变量名 → 类型 *)
Definition type_env : Type := list (ident * st_type).

(* 环境查找 *)
Fixpoint lookup (env : type_env) (x : ident) : option st_type :=
  match env with
  | nil => None
  | (k, v) :: rest =>
      if ident_eq k x then Some v else lookup rest x
  end.

(* 类型检查关系: Γ ⊢ expr : type *)
Inductive has_type : type_env -> st_expr -> st_type -> Prop :=
  | T_Literal : forall ctx l ty,
      literal_type l = Some ty ->
      has_type ctx (E_LIT l) ty
  | T_Var : forall ctx x ty,
      lookup ctx x = Some ty ->
      has_type ctx (E_VAR x) ty
  | T_ArrayAccess : forall ctx arr idx arr_ty idx_ty elem_ty low high,
      has_type ctx arr (T_ARRAY elem_ty low high) ->
      has_type ctx idx T_INT ->
      has_type ctx (E_ARRAY_ACCESS arr idx) elem_ty
  | T_Unary : forall ctx e op ty,
      has_type ctx e ty ->
      is_valid_unary op ty ->
      has_type ctx (E_UNARY_OP op e) ty
  | T_BinOp : forall ctx e1 e2 op ty1 ty2 ty3,
      has_type ctx e1 ty1 ->
      has_type ctx e2 ty2 ->
      promote_type ty1 ty2 ty3 ->
      is_valid_binary op ty3 ->
      has_type ctx (E_BIN_OP op e1 e2) ty3
  | T_Compare : forall ctx e1 e2 op ty1 ty2,
      has_type ctx e1 ty1 ->
      has_type ctx e2 ty2 ->
      type_compatible ty1 ty2 ->
      has_type ctx (E_COMP op e1 e2) T_BOOL
  | T_And : forall ctx e1 e2,
      has_type ctx e1 T_BOOL ->
      has_type ctx e2 T_BOOL ->
      has_type ctx (E_AND e1 e2) T_BOOL
  | T_Or : forall ctx e1 e2,
      has_type ctx e1 T_BOOL ->
      has_type ctx e2 T_BOOL ->
      has_type ctx (E_OR e1 e2) T_BOOL
  | T_Xor : forall ctx e1 e2,
      has_type ctx e1 T_BOOL ->
      has_type ctx e2 T_BOOL ->
      has_type ctx (E_XOR e1 e2) T_BOOL
  | T_FuncCall : forall ctx f args param_types return_type,
      lookup_function ctx f = Some (param_types, return_type) ->
      Forall2 (fun arg ty => has_type ctx arg ty) args param_types ->
      has_type ctx (E_FUNC_CALL f args) return_type
.

(* 一元运算符的有效类型 *)
Definition is_valid_unary (op : unary_op) (ty : st_type) : Prop :=
  match op with
  | U_NEG => ty = T_SINT \/ ty = T_INT \/ ty = T_DINT \/ ty = T_REAL
  | U_NOT => ty = T_BOOL
  | U_ABS => ty = T_SINT \/ ty = T_INT \/ ty = T_DINT \/ ty = T_REAL
  end.

(* 二元运算符的有效类型 *)
Definition is_valid_binary (op : binary_op) (ty : st_type) : Prop :=
  match op with
  | B_ADD => ty = T_INT \/ ty = T_DINT \/ ty = T_REAL
  | B_SUB => ty = T_INT \/ ty = T_DINT \/ ty = T_REAL
  | B_MUL => ty = T_INT \/ ty = T_DINT \/ ty = T_REAL
  | B_DIV => ty = T_INT \/ ty = T_DINT \/ ty = T_REAL
  | B_MOD => ty = T_INT \/ ty = T_DINT
  end.

(* ================================================================
   第 10 部分：良构性定义 (Well-formedness)
   ================================================================ *)

(* 程序良构：所有引用的标识符都已声明，类型正确 *)
Definition well_formed_program (p : st_program) : Prop :=
  (* 1. 无重复声明 *)
  no_duplicate_declarations p /\
  (* 2. 所有引用已声明 *)
  all_refs_declared p /\
  (* 3. 无递归调用 *)
  no_recursive_calls p /\
  (* 4. 函数无副作用 *)
  all_functions_pure p /\
  (* 5. 所有循环有界 *)
  all_loops_bounded p
.

(* 循环有界性 *)
Inductive loop_bounded : st_stmt -> Prop :=
  | Bounded_for : forall v start end_ step body,
      exists n : Z, 0 <= n <= MAX_CYCLE_LIMIT /\
      (* 循环次数 = (end - start) / step + 1 *)
      loop_count start end_ step = Some n ->
      loop_bounded (S_FOR v start end_ step body)
  | Bounded_while : forall cond body,
      (* WHILE 需要有 variant 注解，或限制最大迭代次数 *)
      False ->  (* 待实现：variant 检查 *)
      loop_bounded (S_WHILE cond body)
  | Bounded_repeat : forall body cond,
      False ->
      loop_bounded (S_REPEAT body cond)
  | Bounded_other : forall s,
      (* 非循环语句视为有界 *)
      match s with S_FOR _ _ _ _ _ => False | S_WHILE _ _ => False
                   | S_REPEAT _ _ => False | _ => True end ->
      loop_bounded s
.

Definition MAX_CYCLE_LIMIT : Z := 1000000.

(* 无递归调用 — 通过调用图分析 *)
Definition no_recursive_calls (p : st_program) : Prop :=
  (* 构建调用图，检查无环 *)
  True.  (* 具体实现在 analysis.v 中 *)

(* 函数无副作用 *)
Definition all_functions_pure (p : st_program) : Prop :=
  True.  (* 具体实现在 analysis.v 中 *)

(* ================================================================
   第 11 部分：类型安全定理 (Type Safety Theorem)
   ================================================================ *)

(* Progress: 良类型程序要么是终态，要么可以执行一步 *)
Theorem progress : forall (p : st_program) (env : type_env) (s : st_state),
    well_formed_program p ->
    has_type_program p env ->
    terminal_state s \/ exists s', step p s s'.

(* Preservation: 执行保持类型 *)
Theorem preservation : forall (p : st_program) (env : type_env) (s s' : st_state),
    well_formed_program p ->
    has_type_program p env ->
    step p s s' ->
    has_type_program p env.

(* Type Safety: 良类型程序不会卡住（不产生运行时类型错误） *)
Theorem type_safety : forall (p : st_program) (env : type_env) (s : st_state),
    well_formed_program p ->
    has_type_program p env ->
    exists s', star (step p) s s' /\ terminal_state s'.
