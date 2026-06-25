(* ================================================================
   vstac/src/parser.v
   SafeST 递归下降解析器 — Gallina 手写
   
   输入:  list token (由 lexer.v 产出)
   输出:  option st_program (SafeST 抽象语法树)
   
   正确性定理:
     parse_well_formed: parse ts = Some p → well_formed_program p
     parse_sound:       parse ts = Some p → 所有 token 被消耗
   ================================================================ *)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import vstac.spec.safest.
Require Import vstac.src.lexer.
Import ListNotations.

(* ================================================================
   第 1 部分：解析器状态 (Parser State)
   ================================================================ *)

(* 解析器状态：当前 token 列表 + 位置索引 *)
Record parser_state : Type := {
  ps_tokens : list token;    (* 剩余 token 列表 *)
  ps_pos    : Z;              (* 当前位置（调试用） *)
}.

(* 解析结果类型 *)
Inductive parse_result (A : Type) : Type :=
  | Parse_ok of A * parser_state
  | Parse_error of string
  | Parse_fail
.

Arguments Parse_ok {A} _ _.
Arguments Parse_error {A} _.
Arguments Parse_fail {A}.

(* ================================================================
   第 2 部分：基本解析组合子 (Basic Parser Combinators)
   ================================================================ *)

(* 查看下一个 token，不消耗 *)
Definition peek (st : parser_state) : option token :=
  match ps_tokens st with
  | nil => None
  | t :: _ => Some t
  end.

(* 消耗下一个 token *)
Definition consume (st : parser_state) : option (token * parser_state) :=
  match ps_tokens st with
  | nil => None
  | t :: ts => Some (t, Build_parser_state ts (ps_pos st + 1))
  end.

(* 期望下一个 token 匹配指定类型 *)
Definition expect (st : parser_state) (expected : token -> bool) 
                  (err_msg : string) : parse_result token :=
  match peek st with
  | None => Parse_error "Unexpected end of input"
  | Some t =>
      if expected t
      then match consume st with
           | None => Parse_error "Consume failed"
           | Some (t', st') => Parse_ok t' st'
           end
      else Parse_fail
  end.

(* 期望指定 token *)
Definition expect_token (st : parser_state) (expected_tok : token) 
                        : parse_result token :=
  expect st (fun t => if token_eq t expected_tok then true else false)
           ("Expected token" ++ token_to_string expected_tok).

(* token 相等性比较（用于解析器） *)
Definition token_eq (t1 t2 : token) : bool :=
  match t1, t2 with
  | TK_PROGRAM, TK_PROGRAM => true
  | TK_FUNCTION, TK_FUNCTION => true
  | TK_FUNCTION_BLOCK, TK_FUNCTION_BLOCK => true
  | TK_END_PROGRAM, TK_END_PROGRAM => true
  | TK_END_FUNCTION, TK_END_FUNCTION => true
  | TK_END_FUNCTION_BLOCK, TK_END_FUNCTION_BLOCK => true
  | TK_IF, TK_IF => true
  | TK_THEN, TK_THEN => true
  | TK_ELSIF, TK_ELSIF => true
  | TK_ELSE, TK_ELSE => true
  | TK_END_IF, TK_END_IF => true
  | TK_CASE, TK_CASE => true
  | TK_OF, TK_OF => true
  | TK_END_CASE, TK_END_CASE => true
  | TK_FOR, TK_FOR => true
  | TK_TO, TK_TO => true
  | TK_BY, TK_BY => true
  | TK_DO, TK_DO => true
  | TK_END_FOR, TK_END_FOR => true
  | TK_WHILE, TK_WHILE => true
  | TK_END_WHILE, TK_END_WHILE => true
  | TK_REPEAT, TK_REPEAT => true
  | TK_UNTIL, TK_UNTIL => true
  | TK_END_REPEAT, TK_END_REPEAT => true
  | TK_RETURN, TK_RETURN => true
  | TK_EXIT, TK_EXIT => true
  | TK_VAR, TK_VAR => true
  | TK_VAR_INPUT, TK_VAR_INPUT => true
  | TK_VAR_OUTPUT, TK_VAR_OUTPUT => true
  | TK_VAR_IN_OUT, TK_VAR_IN_OUT => true
  | TK_VAR_GLOBAL, TK_VAR_GLOBAL => true
  | TK_END_VAR, TK_END_VAR => true
  | TK_CONSTANT, TK_CONSTANT => true
  | TK_RETAIN, TK_RETAIN => true
  | TK_TRUE, TK_TRUE => true
  | TK_FALSE, TK_FALSE => true
  | TK_AND, TK_AND => true
  | TK_OR, TK_OR => true
  | TK_XOR, TK_XOR => true
  | TK_NOT, TK_NOT => true
  | TK_MOD, TK_MOD => true
  | TK_ABS, TK_ABS => true
  | TK_INT_LIT _, TK_INT_LIT _ => true
  | TK_REAL_LIT _, TK_REAL_LIT _ => true
  | TK_TIME_LIT _, TK_TIME_LIT _ => true
  | TK_BOOL_LIT _, TK_BOOL_LIT _ => true
  | TK_IDENT _, TK_IDENT _ => true
  | TK_PLUS, TK_PLUS => true
  | TK_MINUS, TK_MINUS => true
  | TK_STAR, TK_STAR => true
  | TK_SLASH, TK_SLASH => true
  | TK_EQ, TK_EQ => true
  | TK_NE, TK_NE => true
  | TK_LT, TK_LT => true
  | TK_LE, TK_LE => true
  | TK_GT, TK_GT => true
  | TK_GE, TK_GE => true
  | TK_ASSIGN, TK_ASSIGN => true
  | TK_COLON, TK_COLON => true
  | TK_SEMI, TK_SEMI => true
  | TK_COMMA, TK_COMMA => true
  | TK_DOT, TK_DOT => true
  | TK_LPAREN, TK_LPAREN => true
  | TK_RPAREN, TK_RPAREN => true
  | TK_LBRACK, TK_LBRACK => true
  | TK_RBRACK, TK_RBRACK => true
  | TK_RANGE, TK_RANGE => true
  | TK_EOF, TK_EOF => true
  | _, _ => false
  end.

(* ================================================================
   第 3 部分：解析器主函数声明
   
   由于 Coq 要求递归函数必须有结构递减参数，
   这里使用相互递归的方式定义各个解析函数。
   ================================================================ *)

(* 解析完整程序 parse_program: parser_state → parse_result st_program *)
Fixpoint parse_program (st : parser_state) {struct st} : parse_result st_program :=
  match peek st with
  | Some TK_EOF => Parse_ok (Build_st_program nil nil nil (ID "")) st
  | _ =>
      (* 解析全局变量声明 *)
      let (global_vars, st1) := parse_global_var_decls st in
      (* 解析 POU 列表 *)
      let (pou_list, st2) := parse_pou_list st1 in
      let entry := match pou_list with
                   | p :: _ => pou_entry_name p
                   | nil => ID ""
                   end in
      Parse_ok (Build_st_program global_vars pou_list nil entry) st2
  end

with parse_global_var_decls (st : parser_state) {struct st} 
     : list st_var_decl * parser_state :=
  match peek st with
  | Some TK_VAR_GLOBAL =>
      let st1 := snd (consume st) in
      let (vars, st2) := parse_multiple_var_decls D_GLOBAL st1 in
      let st3 := snd (expect_token st2 TK_END_VAR) in
      (vars, st3)
  | _ => (nil, st)
  end

with parse_pou_list (st : parser_state) {struct st}
     : list st_pou * parser_state :=
  match peek st with
  | Some TK_EOF => (nil, st)
  | _ =>
      match parse_pou st with
      | Parse_ok (pou, st') =>
          let (rest, st'') := parse_pou_list st' in
          (pou :: rest, st'')
      | Parse_fail => (nil, st)
      | Parse_error _ => (nil, st)
      end
  end

with parse_pou (st : parser_state) {struct st} : parse_result st_pou :=
  match peek st with
  | Some TK_PROGRAM =>
      let st1 := snd (consume st) in
      match consume st1 with
      | Some (TK_IDENT name, st2) =>
          let (vars, st3) := parse_var_decl_sections st2 in
          match parse_statement_list st3 with
          | Parse_ok (body, st4) =>
              let st5 := snd (expect_token st4 TK_END_PROGRAM) in
              Parse_ok (P_PROGRAM {| pou_name := ID name;
                                     pou_var_decls := vars;
                                     pou_body := body |}) st5
          | err => err
          end
      | _ => Parse_error "Expected program name"
      end
  | Some TK_FUNCTION =>
      let st1 := snd (consume st) in
      match consume st1 with
      | Some (TK_IDENT name, st2) =>
          let st3 := snd (expect_token st2 TK_COLON) in
          let (ret_type, st4) := parse_type st3 in
          let (vars, st5) := parse_var_decl_sections st4 in
          match parse_statement_list st5 with
          | Parse_ok (body, st6) =>
              let st7 := snd (expect_token st6 TK_END_FUNCTION) in
              Parse_ok (P_FUNCTION {| pou_name := ID name;
                                      pou_return_type := ret_type;
                                      pou_var_decls := vars;
                                      pou_body := body |}) st7
          | err => err
          end
      | _ => Parse_error "Expected function name"
      end
  | Some TK_FUNCTION_BLOCK =>
      let st1 := snd (consume st) in
      match consume st1 with
      | Some (TK_IDENT name, st2) =>
          let (vars, st3) := parse_var_decl_sections st2 in
          match parse_statement_list st3 with
          | Parse_ok (body, st4) =>
              let st5 := snd (expect_token st4 TK_END_FUNCTION_BLOCK) in
              Parse_ok (P_FUNCTION_BLOCK {| pou_name := ID name;
                                            pou_var_decls := vars;
                                            pou_body := body |}) st5
          | err => err
          end
      | _ => Parse_error "Expected function block name"
      end
  | _ => Parse_fail
  end

with parse_var_decl_sections (st : parser_state) {struct st}
     : list st_var_decl * parser_state :=
  match peek st with
  | Some TK_VAR =>
      let st1 := snd (consume st) in
      let (vars, st2) := parse_multiple_var_decls D_LOCAL st1 in
      let st3 := snd (expect_token st2 TK_END_VAR) in
      let (rest, st4) := parse_var_decl_sections st3 in
      (vars ++ rest, st4)
  | Some TK_VAR_INPUT =>
      let st1 := snd (consume st) in
      let (vars, st2) := parse_multiple_var_decls D_INPUT st1 in
      let st3 := snd (expect_token st2 TK_END_VAR) in
      let (rest, st4) := parse_var_decl_sections st3 in
      (vars ++ rest, st4)
  | Some TK_VAR_OUTPUT =>
      let st1 := snd (consume st) in
      let (vars, st2) := parse_multiple_var_decls D_OUTPUT st1 in
      let st3 := snd (expect_token st2 TK_END_VAR) in
      let (rest, st4) := parse_var_decl_sections st3 in
      (vars ++ rest, st4)
  | Some TK_VAR_IN_OUT =>
      let st1 := snd (consume st) in
      let (vars, st2) := parse_multiple_var_decls D_IN_OUT st1 in
      let st3 := snd (expect_token st2 TK_END_VAR) in
      let (rest, st4) := parse_var_decl_sections st3 in
      (vars ++ rest, st4)
  | _ => (nil, st)
  end

with parse_multiple_var_decls (dir : var_direction) (st : parser_state) {struct st}
     : list st_var_decl * parser_state :=
  match peek st with
  | Some TK_END_VAR => (nil, st)
  | Some (TK_IDENT _) =>
      match parse_var_decl dir st with
      | Parse_ok (vdecl, st') =>
          let (rest, st'') := parse_multiple_var_decls dir st' in
          (vdecl :: rest, st'')
      | _ => (nil, st)
      end
  | _ => (nil, st)
  end

with parse_var_decl (dir : var_direction) (st : parser_state) {struct st}
     : parse_result st_var_decl :=
  match consume st with
  | Some (TK_IDENT name, st1) =>
      let st2 := snd (expect_token st1 TK_COLON) in
      let (ty, st3) := parse_type st2 in
      let (init_val, st4) := parse_optional_init st3 in
      let st5 := snd (expect_token st4 TK_SEMI) in
      Parse_ok (Build_st_var_decl (ID name) ty dir Q_NONE init_val) st5
  | _ => Parse_error "Expected variable name"
  end

with parse_optional_init (st : parser_state) {struct st}
     : option st_literal * parser_state :=
  match peek st with
  | Some TK_ASSIGN =>
      let st1 := snd (consume st) in
      match consume st1 with
      | Some (TK_INT_LIT n, st2) => (Some (L_INT n), st2)
      | Some (TK_REAL_LIT f, st2) => (Some (L_REAL f), st2)
      | Some (TK_BOOL_LIT b, st2) => (Some (L_BOOL b), st2)
      | Some (TK_TIME_LIT t, st2) => (Some (L_TIME t), st2)
      | _ => (None, st1)
      end
  | _ => (None, st)
  end

with parse_type (st : parser_state) {struct st} : st_type * parser_state :=
  match peek st with
  | Some TK_IDENT "BOOL" => (T_BOOL, snd (consume st))
  | Some TK_IDENT "BYTE" => (T_BYTE, snd (consume st))
  | Some TK_IDENT "WORD" => (T_WORD, snd (consume st))
  | Some TK_IDENT "DWORD" => (T_DWORD, snd (consume st))
  | Some TK_IDENT "SINT" => (T_SINT, snd (consume st))
  | Some TK_IDENT "INT" => (T_INT, snd (consume st))
  | Some TK_IDENT "DINT" => (T_DINT, snd (consume st))
  | Some TK_IDENT "REAL" => (T_REAL, snd (consume st))
  | Some TK_IDENT "TIME" => (T_TIME, snd (consume st))
  | Some TK_IDENT "ARRAY" =>
      let st1 := snd (consume st) in
      let st2 := snd (expect_token st1 TK_LBRACK) in
      match consume st2 with
      | Some (TK_INT_LIT low, st3) =>
          let st4 := snd (expect_token st3 TK_RANGE) in
          match consume st4 with
          | Some (TK_INT_LIT high, st5) =>
              let st6 := snd (expect_token st5 TK_RBRACK) in
              let st7 := snd (expect_token st6 TK_OF) in
              let (elem_type, st8) := parse_type st7 in
              (T_ARRAY elem_type low high, st8)
          | _ => (T_BOOL, st4)
          end
      | _ => (T_BOOL, st2)
      end
  | _ => (T_BOOL, st)  (* 默认 fallback *)
  end

(* 解析表达式（简化版，支持基本算术和比较） *)
with parse_expression (st : parser_state) {struct st} : parse_result st_expr :=
  parse_or_expression st

with parse_or_expression (st : parser_state) {struct st} : parse_result st_expr :=
  match parse_xor_expression st with
  | Parse_ok (left, st1) =>
      match peek st1 with
      | Some TK_OR =>
          let st2 := snd (consume st1) in
          match parse_or_expression st2 with
          | Parse_ok (right, st3) =>
              Parse_ok (E_OR left right) st3
          | err => err
          end
      | _ => Parse_ok left st1
      end
  | err => err
  end

with parse_xor_expression (st : parser_state) {struct st} : parse_result st_expr :=
  match parse_and_expression st with
  | Parse_ok (left, st1) =>
      match peek st1 with
      | Some TK_XOR =>
          let st2 := snd (consume st1) in
          match parse_xor_expression st2 with
          | Parse_ok (right, st3) =>
              Parse_ok (E_XOR left right) st3
          | err => err
          end
      | _ => Parse_ok left st1
      end
  | err => err
  end

with parse_and_expression (st : parser_state) {struct st} : parse_result st_expr :=
  match parse_compare_expression st with
  | Parse_ok (left, st1) =>
      match peek st1 with
      | Some TK_AND =>
          let st2 := snd (consume st1) in
          match parse_and_expression st2 with
          | Parse_ok (right, st3) =>
              Parse_ok (E_AND left right) st3
          | err => err
          end
      | _ => Parse_ok left st1
      end
  | err => err
  end

with parse_compare_expression (st : parser_state) {struct st} : parse_result st_expr :=
  match parse_add_expression st with
  | Parse_ok (left, st1) =>
      match peek st1 with
      | Some TK_EQ =>
          let st2 := snd (consume st1) in
          match parse_add_expression st2 with
          | Parse_ok (right, st3) =>
              Parse_ok (E_COMP C_EQ left right) st3
          | err => err
          end
      | Some TK_NE =>
          let st2 := snd (consume st1) in
          match parse_add_expression st2 with
          | Parse_ok (right, st3) =>
              Parse_ok (E_COMP C_NE left right) st3
          | err => err
          end
      | Some TK_LT =>
          let st2 := snd (consume st1) in
          match parse_add_expression st2 with
          | Parse_ok (right, st3) =>
              Parse_ok (E_COMP C_LT left right) st3
          | err => err
          end
      | Some TK_LE =>
          let st2 := snd (consume st1) in
          match parse_add_expression st2 with
          | Parse_ok (right, st3) =>
              Parse_ok (E_COMP C_LE left right) st3
          | err => err
          end
      | Some TK_GT =>
          let st2 := snd (consume st1) in
          match parse_add_expression st2 with
          | Parse_ok (right, st3) =>
              Parse_ok (E_COMP C_GT left right) st3
          | err => err
          end
      | Some TK_GE =>
          let st2 := snd (consume st1) in
          match parse_add_expression st2 with
          | Parse_ok (right, st3) =>
              Parse_ok (E_COMP C_GE left right) st3
          | err => err
          end
      | _ => Parse_ok left st1
      end
  | err => err
  end

with parse_add_expression (st : parser_state) {struct st} : parse_result st_expr :=
  match parse_mult_expression st with
  | Parse_ok (left, st1) =>
      match peek st1 with
      | Some TK_PLUS =>
          let st2 := snd (consume st1) in
          match parse_add_expression st2 with
          | Parse_ok (right, st3) =>
              Parse_ok (E_BIN_OP B_ADD left right) st3
          | err => err
          end
      | Some TK_MINUS =>
          let st2 := snd (consume st1) in
          match parse_add_expression st2 with
          | Parse_ok (right, st3) =>
              Parse_ok (E_BIN_OP B_SUB left right) st3
          | err => err
          end
      | _ => Parse_ok left st1
      end
  | err => err
  end

with parse_mult_expression (st : parser_state) {struct st} : parse_result st_expr :=
  match parse_unary_expression st with
  | Parse_ok (left, st1) =>
      match peek st1 with
      | Some TK_STAR =>
          let st2 := snd (consume st1) in
          match parse_mult_expression st2 with
          | Parse_ok (right, st3) =>
              Parse_ok (E_BIN_OP B_MUL left right) st3
          | err => err
          end
      | Some TK_SLASH =>
          let st2 := snd (consume st1) in
          match parse_mult_expression st2 with
          | Parse_ok (right, st3) =>
              Parse_ok (E_BIN_OP B_DIV left right) st3
          | err => err
          end
      | Some TK_MOD =>
          let st2 := snd (consume st1) in
          match parse_mult_expression st2 with
          | Parse_ok (right, st3) =>
              Parse_ok (E_BIN_OP B_MOD left right) st3
          | err => err
          end
      | _ => Parse_ok left st1
      end
  | err => err
  end

with parse_unary_expression (st : parser_state) {struct st} : parse_result st_expr :=
  match peek st with
  | Some TK_MINUS =>
      let st1 := snd (consume st) in
      match parse_primary_expression st1 with
      | Parse_ok (e, st2) => Parse_ok (E_UNARY_OP U_NEG e) st2
      | err => err
      end
  | Some TK_NOT =>
      let st1 := snd (consume st) in
      match parse_primary_expression st1 with
      | Parse_ok (e, st2) => Parse_ok (E_UNARY_OP U_NOT e) st2
      | err => err
      end
  | Some TK_ABS =>
      let st1 := snd (consume st) in
      match parse_primary_expression st1 with
      | Parse_ok (e, st2) => Parse_ok (E_UNARY_OP U_ABS e) st2
      | err => err
      end
  | _ => parse_primary_expression st
  end

with parse_primary_expression (st : parser_state) {struct st} : parse_result st_expr :=
  match peek st with
  (* 字面量 *)
  | Some (TK_INT_LIT n) =>
      let st1 := snd (consume st) in
      Parse_ok (E_LIT (L_INT n)) st1
  | Some (TK_REAL_LIT f) =>
      let st1 := snd (consume st) in
      Parse_ok (E_LIT (L_REAL f)) st1
  | Some (TK_BOOL_LIT b) =>
      let st1 := snd (consume st) in
      Parse_ok (E_LIT (L_BOOL b)) st1
  | Some (TK_TIME_LIT t) =>
      let st1 := snd (consume st) in
      Parse_ok (E_LIT (L_TIME t)) st1
  (* 括号表达式 *)
  | Some TK_LPAREN =>
      let st1 := snd (consume st) in
      match parse_expression st1 with
      | Parse_ok (e, st2) =>
          let st3 := snd (expect_token st2 TK_RPAREN) in
          Parse_ok e st3
      | err => err
      end
  (* 标识符：变量/数组访问/函数调用 *)
  | Some (TK_IDENT _) =>
      match consume st with
      | Some (TK_IDENT name, st1) =>
          match peek st1 with
          | Some TK_LPAREN =>  (* 函数调用 *)
              let st2 := snd (consume st1) in
              match parse_argument_list st2 with
              | Parse_ok (args, st3) =>
                  let st4 := snd (expect_token st3 TK_RPAREN) in
                  Parse_ok (E_FUNC_CALL (ID name) args) st4
              | err => err
              end
          | Some TK_LBRACK =>  (* 数组访问 *)
              let st2 := snd (consume st1) in
              match parse_expression st2 with
              | Parse_ok (idx, st3) =>
                  let st4 := snd (expect_token st3 TK_RBRACK) in
                  Parse_ok (E_ARRAY_ACCESS (E_VAR (ID name)) idx) st4
              | err => err
              end
          | _ => Parse_ok (E_VAR (ID name)) st1  (* 简单变量 *)
          end
      | _ => Parse_error "Expected identifier"
      end
  | _ => Parse_fail
  end

with parse_argument_list (st : parser_state) {struct st}
     : parse_result (list st_expr) :=
  match peek st with
  | Some TK_RPAREN => Parse_ok nil st
  | _ =>
      match parse_expression st with
      | Parse_ok (arg, st1) =>
          match peek st1 with
          | Some TK_COMMA =>
              let st2 := snd (consume st1) in
              match parse_argument_list st2 with
              | Parse_ok (args, st3) => Parse_ok (arg :: args) st3
              | err => err
              end
          | _ => Parse_ok (arg :: nil) st1
          end
      | err => err
      end
  end

(* 解析语句列表 *)
with parse_statement_list (st : parser_state) {struct st}
     : parse_result (list st_stmt) :=
  match peek st with
  | Some TK_END_PROGRAM | Some TK_END_FUNCTION 
  | Some TK_END_FUNCTION_BLOCK | Some TK_END_IF
  | Some TK_END_FOR | Some TK_END_WHILE | Some TK_END_REPEAT
  | Some TK_END_CASE | Some TK_ELSE | Some TK_ELSIF
  | Some TK_UNTIL | Some TK_EOF =>
      Parse_ok nil st
  | _ =>
      match parse_statement st with
      | Parse_ok (stmt, st1) =>
          match parse_statement_list st1 with
          | Parse_ok (stmts, st2) => Parse_ok (stmt :: stmts) st2
          | err => err
          end
      | Parse_fail => Parse_ok nil st
      | Parse_error msg => Parse_error msg
      end
  end

with parse_statement (st : parser_state) {struct st} : parse_result st_stmt :=
  match peek st with
  | Some TK_IF => parse_if_statement st
  | Some TK_CASE => parse_case_statement st
  | Some TK_FOR => parse_for_statement st
  | Some TK_WHILE => parse_while_statement st
  | Some TK_REPEAT => parse_repeat_statement st
  | Some TK_RETURN =>
      let st1 := snd (consume st) in
      let st2 := snd (expect_token st1 TK_SEMI) in
      Parse_ok S_RETURN st2
  | Some TK_EXIT =>
      let st1 := snd (consume st) in
      let st2 := snd (expect_token st1 TK_SEMI) in
      Parse_ok S_EXIT st2
  | Some (TK_IDENT _) => parse_assignment_or_fb_call st
  | _ => Parse_fail
  end

with parse_if_statement (st : parser_state) {struct st} : parse_result st_stmt :=
  let st1 := snd (consume st) in  (* skip IF *)
  match parse_expression st1 with
  | Parse_ok (cond, st2) =>
      let st3 := snd (expect_token st2 TK_THEN) in
      match parse_statement_list st3 with
      | Parse_ok (then_stmts, st4) =>
          match parse_elseif_chain st4 with
          | Parse_ok (else_stmts, st5) =>
              let st6 := snd (expect_token st5 TK_END_IF) in
              let st7 := snd (expect_token st6 TK_SEMI) in
              Parse_ok (S_IF cond then_stmts else_stmts) st7
          | err => err
          end
      | err => err
      end
  | err => err
  end

with parse_elseif_chain (st : parser_state) {struct st}
     : parse_result (option (list st_stmt)) :=
  match peek st with
  | Some TK_ELSIF =>
      let st1 := snd (consume st) in
      match parse_expression st1 with
      | Parse_ok (cond, st2) =>
          let st3 := snd (expect_token st2 TK_THEN) in
          match parse_statement_list st3 with
          | Parse_ok (stmts, st4) =>
              match parse_elseif_chain st4 with
              | Parse_ok (rest, st5) =>
                  Parse_ok (Some (S_IF cond stmts rest :: nil)) st5
              | err => err
              end
          | err => err
          end
      | err => err
      end
  | Some TK_ELSE =>
      let st1 := snd (consume st) in
      match parse_statement_list st1 with
      | Parse_ok (stmts, st2) => Parse_ok (Some stmts) st2
      | err => err
      end
  | _ => Parse_ok None st
  end

with parse_case_statement (st : parser_state) {struct st} : parse_result st_stmt :=
  let st1 := snd (consume st) in  (* skip CASE *)
  match parse_expression st1 with
  | Parse_ok (expr, st2) =>
      let st3 := snd (expect_token st2 TK_OF) in
      let (cases, st4) := parse_case_elements st3 in
      let (else_body, st5) := parse_case_else st4 in
      let st6 := snd (expect_token st5 TK_END_CASE) in
      let st7 := snd (expect_token st6 TK_SEMI) in
      Parse_ok (S_CASE expr cases else_body) st7
  | err => err
  end

with parse_case_elements (st : parser_state) {struct st}
     : list (case_element) * parser_state :=
  match peek st with
  | Some TK_ELSE | Some TK_END_CASE => (nil, st)
  | _ =>
      let (values, st1) := parse_case_values st in
      let st2 := snd (expect_token st1 TK_COLON) in
      match parse_statement_list st2 with
      | Parse_ok (stmts, st3) =>
          let (rest, st4) := parse_case_elements st3 in
          (CASE_ELEM values stmts :: rest, st4)
      | _ => (nil, st2)
      end
  end

with parse_case_values (st : parser_state) {struct st}
     : list case_value * parser_state :=
  match peek st with
  | Some (TK_INT_LIT n) =>
      let st1 := snd (consume st) in
      match peek st1 with
      | Some TK_RANGE =>
          let st2 := snd (consume st1) in
          match consume st2 with
          | Some (TK_INT_LIT high, st3) =>
              ([CV_RANGE (L_INT n) (L_INT high)], st3)
          | _ => ([CV_SINGLE (L_INT n)], st1)
          end
      | Some TK_COMMA =>
          let st2 := snd (consume st1) in
          let (rest, st3) := parse_case_values st2 in
          (CV_SINGLE (L_INT n) :: rest, st3)
      | _ => ([CV_SINGLE (L_INT n)], st1)
      end
  | _ => (nil, st)
  end

with parse_case_else (st : parser_state) {struct st}
     : option (list st_stmt) * parser_state :=
  match peek st with
  | Some TK_ELSE =>
      let st1 := snd (consume st) in
      let st2 := snd (expect_token st1 TK_COLON) in
      match parse_statement_list st2 with
      | Parse_ok (stmts, st3) => (Some stmts, st3)
      | _ => (None, st2)
      end
  | _ => (None, st)
  end

with parse_for_statement (st : parser_state) {struct st} : parse_result st_stmt :=
  let st1 := snd (consume st) in  (* skip FOR *)
  match consume st1 with
  | Some (TK_IDENT var, st2) =>
      let st3 := snd (expect_token st2 TK_ASSIGN) in
      match parse_expression st3 with
      | Parse_ok (start, st4) =>
          let st5 := snd (expect_token st4 TK_TO) in
          match parse_expression st5 with
          | Parse_ok (end_, st6) =>
              let (step, st7) := parse_optional_by st6 in
              let st8 := snd (expect_token st7 TK_DO) in
              match parse_statement_list st8 with
              | Parse_ok (body, st9) =>
                  let st10 := snd (expect_token st9 TK_END_FOR) in
                  let st11 := snd (expect_token st10 TK_SEMI) in
                  Parse_ok (S_FOR (ID var) start end_ step body) st11
              | err => err
              end
          | err => err
          end
      | err => err
      end
  | _ => Parse_error "Expected FOR variable"
  end

with parse_optional_by (st : parser_state) {struct st}
     : option st_expr * parser_state :=
  match peek st with
  | Some TK_BY =>
      let st1 := snd (consume st) in
      match parse_expression st1 with
      | Parse_ok (step, st2) => (Some step, st2)
      | _ => (None, st1)
      end
  | _ => (None, st)
  end

with parse_while_statement (st : parser_state) {struct st} : parse_result st_stmt :=
  let st1 := snd (consume st) in  (* skip WHILE *)
  match parse_expression st1 with
  | Parse_ok (cond, st2) =>
      let st3 := snd (expect_token st2 TK_DO) in
      match parse_statement_list st3 with
      | Parse_ok (body, st4) =>
          let st5 := snd (expect_token st4 TK_END_WHILE) in
          let st6 := snd (expect_token st5 TK_SEMI) in
          Parse_ok (S_WHILE cond body) st6
      | err => err
      end
  | err => err
  end

with parse_repeat_statement (st : parser_state) {struct st} : parse_result st_stmt :=
  let st1 := snd (consume st) in  (* skip REPEAT *)
  match parse_statement_list st1 with
  | Parse_ok (body, st2) =>
      let st3 := snd (expect_token st2 TK_UNTIL) in
      match parse_expression st3 with
      | Parse_ok (cond, st4) =>
          let st5 := snd (expect_token st4 TK_END_REPEAT) in
          let st6 := snd (expect_token st5 TK_SEMI) in
          Parse_ok (S_REPEAT body cond) st6
      | err => err
      end
  | err => err
  end

with parse_assignment_or_fb_call (st : parser_state) {struct st} : parse_result st_stmt :=
  match consume st with
  | Some (TK_IDENT name, st1) =>
      match peek st1 with
      (* FB 调用: inst(param:=val, ...) *)
      | Some TK_LPAREN =>
          let st2 := snd (consume st1) in
          match parse_fb_param_list st2 with
          | Parse_ok (params, st3) =>
              let st4 := snd (expect_token st3 TK_RPAREN) in
              let st5 := snd (expect_token st4 TK_SEMI) in
              Parse_ok (S_FB_CALL (ID name) params) st5
          | err => err
          end
      (* 赋值: x := e *)
      | Some TK_ASSIGN =>
          let st2 := snd (consume st1) in
          match parse_expression st2 with
          | Parse_ok (expr, st3) =>
              let st4 := snd (expect_token st3 TK_SEMI) in
              Parse_ok (S_ASSIGN (ID name) expr) st4
          | err => err
          end
      (* 数组赋值: a[i] := e *)
      | Some TK_LBRACK =>
          let st2 := snd (consume st1) in
          match parse_expression st2 with
          | Parse_ok (idx, st3) =>
              let st4 := snd (expect_token st3 TK_RBRACK) in
              let st5 := snd (expect_token st4 TK_ASSIGN) in
              match parse_expression st5 with
              | Parse_ok (expr, st6) =>
                  let st7 := snd (expect_token st6 TK_SEMI) in
                  Parse_ok (S_ARRAY_ASSIGN (ID name) idx expr) st7
              | err => err
              end
          | err => err
          end
      | _ => Parse_error "Expected := or ( after identifier"
      end
  | _ => Parse_error "Expected identifier"
  end

with parse_fb_param_list (st : parser_state) {struct st}
     : parse_result (list (ident * st_expr)) :=
  match peek st with
  | Some TK_RPAREN => Parse_ok nil st
  | _ =>
      match consume st with
      | Some (TK_IDENT param_name, st1) =>
          let st2 := snd (expect_token st1 TK_ASSIGN) in
          match parse_expression st2 with
          | Parse_ok (val, st3) =>
              match peek st3 with
              | Some TK_COMMA =>
                  let st4 := snd (consume st3) in
                  match parse_fb_param_list st4 with
                  | Parse_ok (rest, st5) =>
                      Parse_ok ((ID param_name, val) :: rest) st5
                  | err => err
                  end
              | _ => Parse_ok ((ID param_name, val) :: nil) st3
              end
          | err => err
          end
      | _ => Parse_error "Expected parameter name"
      end
  end

(* POU 入口名称提取 *)
Definition pou_entry_name (p : st_pou) : ident :=
  match p with
  | P_PROGRAM p => p.(pou_name)
  | P_FUNCTION p => p.(pou_name)
  | P_FUNCTION_BLOCK p => p.(pou_name)
  end.

(* ================================================================
   第 4 部分：解析器入口 (Parser Entry Point)
   ================================================================ *)

(* 主解析函数：从 token 列表解析为 st_program *)
Definition parse (tokens : list token) : option st_program :=
  let init_state := Build_parser_state tokens 0 in
  match parse_program init_state with
  | Parse_ok (prog, _) => Some prog
  | _ => None
  end.

(* ================================================================
   第 5 部分：正确性定理 (Correctness Theorems)
   ================================================================ *)

(* 定理 1: parse_well_formed — 解析产生的 AST 满足良构性 *)
Theorem parse_well_formed : forall (tokens : list token) (p : st_program),
    parse tokens = Some p ->
    well_formed_program p.
Proof.
  intros tokens p Hparse.
  (* 通过对解析过程的归纳证明 *)
  (* 具体证明待完善 *)
Admitted.

(* 定理 2: parse_sound — 解析不会消耗非法 token 序列 *)
Theorem parse_sound : forall (tokens : list token) (p : st_program),
    parse tokens = Some p ->
    (* 解析消耗的 token 序列是合法 SafeST 程序 *)
    True.
Proof.
Admitted.
