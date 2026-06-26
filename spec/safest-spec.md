# SafeST — IEC 61131-3 Structured Text 安全子集规范

> **文档版本**：v0.1  
> **状态**：草案  
> **对应 Coq 文件**：`vstac/spec/safest.v`  
> **本文件是顶层规范，Coq 定义是其形式化镜像**

---

## 1. 概述

SafeST 是 IEC 61131-3 标准中 Structured Text (ST) 语言的一个**安全关键子集**。本规范定义它的词法结构、语法、类型系统和安全约束。所有 SafeST 程序均可由 vstac 编译器编译为 SafeASM 字节码，且编译正确性已在 Coq 中形式化证明。

### 1.1 设计原则

1. **最小完备**：足够表达安全级仪控系统的控制逻辑（布尔逻辑、算术运算、定时器、计数器、PID 等）
2. **静态安全**：所有资源分配在编译期完成，无动态内存、无指针、无递归
3. **可验证**：每个语法构造都有明确的 Coq 语义模型，可进行形式化推理
4. **确定终止**：所有循环都有编译期可确定的终止条件或最大迭代次数

---

## 2. 词法规范 (Lexical Structure)

### 2.1 字符集

SafeST 源文件使用 **UTF-8 编码**（仅限 ASCII 子集用于关键字和标识符，字面量可使用 Unicode）。

### 2.2 关键字

以下为 SafeST 保留关键字，不可用作标识符：

```
PROGRAM      FUNCTION     FUNCTION_BLOCK
IF           THEN         ELSIF        ELSE         END_IF
CASE         OF           ELSE         END_CASE
FOR          TO           BY           DO           END_FOR
WHILE        DO           END_WHILE
REPEAT       UNTIL        END_REPEAT
RETURN       EXIT
VAR          VAR_INPUT    VAR_OUTPUT   VAR_IN_OUT   END_VAR
CONSTANT     RETAIN
TRUE         FALSE
AND          OR           XOR          NOT
MOD          ABS
```

**显式排除的关键字**（标准 IEC 61131-3 中有但 SafeST 不支持的）：

```
STRING, WSTRING, REF, REF_TO, POINTER, ARRAY[*], __NEW, __DELETE,
METHOD, PROPERTY, INTERFACE, CLASS, ACTION, TRANSITION, STEP,
SFC 相关全部关键字
```

### 2.3 标识符

```
标识符 := 字母 (字母 | 数字 | 下划线)*
字母   := 'a'..'z' | 'A'..'Z'
数字   := '0'..'9'
```

约束：
- 最大长度：**32 字符**
- 不区分大小写（`MyVar` = `MYVAR` = `myvar`）
- 以下划线开头保留给系统变量
- 关键字不可用作标识符

### 2.4 字面量

```
整数字面量  := 十进制数字序列 (例: 42, -5, 0)
	       | 2#二进制数字序列  (例: 2#1010)
	       | 16#十六进制数字序列 (例: 16#FF)
实数字面量  := 十进制数字序列 . 十进制数字序列 [E [+|-] 十进制数字序列]
	       (例: 3.14, -0.5, 2.0E+3)
布尔字面量  := TRUE | FALSE
时间字面量  := T# 数字 [d|h|m|s|ms]
	       (例: T#5s, T#100ms, T#1h30m)
```

### 2.5 运算符

```
算术:      +  -  *  /  MOD
比较:      =  <>  <  >  <=  >=
逻辑:      AND  OR  XOR  NOT
赋值:      :=
其他:      ..  (范围运算符, CASE 中使用)
```

---

## 3. 语法规范 (Syntax / AST)

### 3.1 基本类型

```ebnf
<type> ::= BOOL
         | BYTE | WORD | DWORD
         | SINT | INT | DINT
         | REAL
         | TIME
         | ARRAY '[' <low> '..' <high> ']' OF <type>
```

| 类型 | 位宽 | 范围 |
|------|------|------|
| BOOL | 1 | TRUE / FALSE |
| BYTE | 8 | 0..255 |
| WORD | 16 | 0..65535 |
| DWORD | 32 | 0..4294967295 |
| SINT | 8 | -128..127 |
| INT | 16 | -32768..32767 |
| DINT | 32 | -2147483648..2147483647 |
| REAL | 32 | IEEE 754 单精度 |
| TIME | 64 | 纳秒计数，0..2^63-1 |

**数组约束**：
- 仅支持**静态数组**（上下界为编译期常量）
- 最多 **3 维**
- 禁止可变长度数组

### 3.2 表达式 (Expressions)

```ebnf
<literal>     ::= <integer_literal> | <real_literal> | <bool_literal> | <time_literal>
<primary>     ::= <literal> | <identifier> | <identifier> '[' <expr> ']'
<unary_expr>  ::= <primary>
                 | '-' <unary_expr>
                 | NOT <unary_expr>
                 | ABS <unary_expr>
<mult_expr>   ::= <unary_expr>
                 | <mult_expr> '*' <unary_expr>
                 | <mult_expr> '/' <unary_expr>
                 | <mult_expr> MOD <unary_expr>
<add_expr>    ::= <mult_expr>
                 | <add_expr> '+' <mult_expr>
                 | <add_expr> '-' <mult_expr>
<compare_expr> ::= <add_expr>
                 | <add_expr> '=' <add_expr>
                 | <add_expr> '<>' <add_expr>
                 | <add_expr> '<' <add_expr>
                 | <add_expr> '<=' <add_expr>
                 | <add_expr> '>' <add_expr>
                 | <add_expr> '>=' <add_expr>
<and_expr>    ::= <compare_expr>
                 | <and_expr> AND <compare_expr>
<xor_expr>    ::= <and_expr>
                 | <xor_expr> XOR <and_expr>
<or_expr>     ::= <xor_expr>
                 | <or_expr> OR <xor_expr>
<expr>        ::= <or_expr>
```

**优先级**（从高到低）：

| 优先级 | 运算符 | 结合性 |
|--------|--------|--------|
| 1 (最高) | `-` (负号) `NOT` `ABS` | 右 |
| 2 | `*` `/` `MOD` | 左 |
| 3 | `+` `-` | 左 |
| 4 | `=` `<>` `<` `<=` `>` `>=` | 左 |
| 5 | `AND` | 左 |
| 6 | `XOR` | 左 |
| 7 (最低) | `OR` | 左 |

### 3.3 语句 (Statements)

```ebnf
<stmt> ::= <identifier> ':=' <expr> ';'                      (* 赋值 *)
         | <identifier> '[' <expr> ']' ':=' <expr> ';'       (* 数组赋值 *)
         | <identifier> '(' <fb_param_list> ')' ';'           (* FB 调用 *)
         | IF <expr> THEN <stmt_list>                         (* IF 语句 *)
           {ELSIF <expr> THEN <stmt_list>}
           [ELSE <stmt_list>]
           END_IF ';'
         | CASE <expr> OF                                      (* CASE 语句 *)
             <case_element>+
           [ELSE <stmt_list>]
           END_CASE ';'
         | FOR <identifier> ':=' <expr> TO <expr>              (* FOR 循环 *)
           [BY <expr>] DO <stmt_list>
           END_FOR ';'
         | WHILE <expr> DO <stmt_list> END_WHILE ';'          (* WHILE 循环 *)
         | REPEAT <stmt_list> UNTIL <expr> END_REPEAT ';'     (* REPEAT 循环 *)
         | RETURN ';'                                          (* 提前返回 *)
         | EXIT ';'                                            (* 退出循环 *)

<stmt_list> ::= <stmt>*

<fb_param_list> ::= <identifier> ':=' <expr> {',' <identifier> ':=' <expr>}
<case_element> ::= <case_value> {',' <case_value>} ':' <stmt_list>
<case_value> ::= <literal> | <literal> '..' <literal>
```

### 3.4 程序组织单元 (POU)

```ebnf
<program> ::= PROGRAM <identifier>
              <var_decl_section>*
              <stmt_list>
              END_PROGRAM

<function> ::= FUNCTION <identifier> ':' <type>
               <var_decl_section>*
               <stmt_list>
               END_FUNCTION

<function_block> ::= FUNCTION_BLOCK <identifier>
                     <var_decl_section>*
                     <stmt_list>
                     END_FUNCTION_BLOCK

<var_decl_section> ::= VAR [CONSTANT | RETAIN]           (* 局部变量 *)
                       <var_decl>+
                       END_VAR
                     | VAR_INPUT                          (* 输入变量 *)
                       <var_decl>+
                       END_VAR
                     | VAR_OUTPUT                         (* 输出变量 *)
                       <var_decl>+
                       END_VAR
                     | VAR_IN_OUT                         (* 输入输出变量 *)
                       <var_decl>+
                       END_VAR

<var_decl> ::= <identifier> {',' <identifier>} ':' <type> [':= <literal>']
<global_var_decl> ::= VAR_GLOBAL [RETAIN]
                       <var_decl>+
                       END_VAR
```

### 3.5 完整程序结构

```ebnf
<safe_st_program> ::= <global_var_decl_section>*
                      <pou>+
```

---

## 4. 类型系统 (Type System)

### 4.1 类型兼容性规则

```
整数类型（SINT/INT/DINT）之间可隐式转换：
  SINT → INT → DINT  (提升方向)

位串类型（BYTE/WORD/DWORD）之间可隐式转换：
  BYTE → WORD → DWORD (提升方向)

整数与位串之间不可隐式转换（需显式转换函数）

REAL 与整数之间不可隐式转换（需显式转换函数）

BOOL 仅与 BOOL 兼容

数组类型要求维度、元素类型完全一致才兼容
```

### 4.2 类型检查规则（语义）

```
Γ ⊢ literal : literal_type(literal)       (T_Literal)

Γ(x) = T                                (T_Var)
Γ ⊢ x : T

Γ ⊢ e1 : T1    Γ ⊢ e2 : T2    promote(T1,T2) = T3
T3 支持 + 操作                                (T_Add)
Γ ⊢ e1 + e2 : T3

Γ ⊢ e : T      T 支持 NOT 操作               (T_Not)
Γ ⊢ NOT e : T

Γ ⊢ e1 : T1    Γ ⊢ e2 : T2
comparable(T1, T2)                          (T_Compare)
Γ ⊢ e1 = e2 : BOOL

Γ ⊢ e : BOOL                                (T_If)
Γ ⊢ IF e THEN ... : OK

Γ ⊢ e1 : INT     Γ ⊢ v : INT
Γ ⊢ e1 TO v : INT                          (T_For)
```

---

## 5. 安全约束 (Safety Constraints)

### S1: 循环有界性

```
FOR 循环：
  编译期推导循环次数 = (end - start) / step + 1
  若 step > 0 且 end ≥ start，次数 ≤ MAX_CYCLE_LIMIT
  若 step < 0 且 end ≤ start，次数 ≤ MAX_CYCLE_LIMIT

WHILE 和 REPEAT 循环：
  需要提供 Loop Variant 注解（编译期检查递减性）
  若无注解，编译器默认插入最大次数限制
```

### S2: 数组边界安全

```
所有数组访问 a[i] 必须在编译期或运行期进行边界检查：
- 编译期：若 i 为编译期常量，直接检查 low ≤ i ≤ high
- 运行期：编译器在生成的 SafeASM 中插入 BOUNDS_CHECK 指令
```

### S3: 禁止递归

```
函数和 FB 不得直接或间接调用自身。
编译器通过调用图分析进行静态检查。
```

### S4: 函数无副作用

```
FUNCTION 不得修改全局变量或 VAR_OUTPUT 变量。
FUNCTION_BLOCK 可以修改自身实例的 VAR_OUTPUT。
```

### S5: 静态实例化

```
所有 FB 实例必须在编译期声明（VAR 块中），
禁止动态创建/销毁 FB 实例。
```

### S6: 除零保护

```
所有除法 / 和 MOD 操作在 SafeASM 生成时插入零值检查。
```

### S7: 类型安全

```
所有变量和表达式在编译期进行类型检查，
禁止运行时类型错误。（Coq 中已证明 type_safety 定理）
```

---

## 6. 内置函数 (Built-in Functions)

SafeST 提供以下内置函数（在 Coq 中预先定义语义）：

| 函数 | 签名 | 说明 |
|------|------|------|
| `ABS` | `ANY_INT → ANY_INT` 或 `REAL → REAL` | 绝对值 |
| `SQRT` | `REAL → REAL` | 平方根 |
| `SIN` | `REAL → REAL` | 正弦 |
| `COS` | `REAL → REAL` | 余弦 |
| `MOVE` | `T → T` | 类型安全的值拷贝 |
| `SEL` | `BOOL, T, T → T` | 选择器 (SEL(g,a,b) = g?a:b) |
| `MUX` | `INT, T... → T` | 多路选择 |

---

## 7. SafeST 语法限制总结

| 特性 | IEC 61131-3 ST | SafeST |
|------|---------------|--------|
| 数据类型 | 全部 + 用户自定义 | BOOL/BYTE/WORD/DWORD/SINT/INT/DINT/REAL/TIME/ARRAY |
| 数组 | 静态+动态 | 仅静态（编译期固定边界） |
| 指针/引用 | REF, REF_TO, POINTER | ❌ 禁止 |
| 字符串 | STRING, WSTRING | ❌ 禁止 |
| 类/方法 | CLASS, METHOD, PROPERTY | ❌ 禁止 |
| SFC | STEP, TRANSITION, ACTION | ❌ 禁止 |
| 动态内存 | __NEW, __DELETE | ❌ 禁止 |
| 递归 | 允许 | ❌ 禁止 |
| 函数重载 | 允许 | ❌ 禁止 |
| 多任务 | 允许 | ❌ 禁止（单任务周期扫描） |
| 异常处理 | 允许 | ❌ 禁止 |
| 循环 | 任意 | ✅ 有界循环（编译期可推导上限） |
| FB 实例化 | 静态+动态 | ✅ 仅静态 |
| 类型检查 | 运行时+编译期 | ✅ 仅编译期（运行时无类型错误） |

---

## 附录 A：SafeST 程序示例

```iecst
(* ================================================================
   示例 1: 简单的起保停电路 (Start-Stop Latch)
   ================================================================ *)
PROGRAM StartStopLatch
    VAR_INPUT
        Start : BOOL := FALSE;
        Stop  : BOOL := FALSE;
    END_VAR
    VAR_OUTPUT
        Run   : BOOL := FALSE;
    END_VAR
    
    Run := (Run OR Start) AND NOT Stop;
END_PROGRAM

(* ================================================================
   示例 2: 定时器 + 计数器
   ================================================================ *)
PROGRAM TimerCounter
    VAR_INPUT
        Trigger : BOOL;
        Reset   : BOOL;
    END_VAR
    VAR_OUTPUT
        Q       : BOOL;
        Elapsed : TIME;
        Count   : INT := 0;
    END_VAR
    VAR
        Running : BOOL := FALSE;
        StartTime : TIME;
    END_VAR
    
    IF Trigger AND NOT Running THEN
        Running := TRUE;
        StartTime := T#0ms;
    END_IF
    
    IF Running THEN
        Elapsed := Elapsed + T#100ms;
        IF Elapsed >= T#5s THEN
            Running := FALSE;
            Q := TRUE;
            Count := Count + 1;
            Elapsed := T#0ms;
        END_IF
    END_IF
    
    IF Reset THEN
        Count := 0;
        Q := FALSE;
        Running := FALSE;
        Elapsed := T#0ms;
    END_IF
END_PROGRAM

(* ================================================================
   示例 3: 数组求和 + FOR 循环
   ================================================================ *)
FUNCTION ArraySum : INT
    VAR_INPUT
        Data : ARRAY[0..9] OF INT;
    END_VAR
    VAR
        i : INT;
        sum : INT := 0;
    END_VAR
    
    FOR i := 0 TO 9 DO
        sum := sum + Data[i];
    END_FOR
    
    ArraySum := sum;
END_FUNCTION

(* ================================================================
   示例 4: IF-CASE 控制逻辑
   ================================================================ *)
FUNCTION_BLOCK ValveControl
    VAR_INPUT
        Pressure : REAL;
        Level    : REAL;
    END_VAR
    VAR_OUTPUT
        ValveOpen  : BOOL;
        Alarm      : BOOL;
    END_VAR
    VAR
        Mode : INT := 0;
    END_VAR
    
    IF Pressure > 10.0 THEN
        Mode := 1;
    ELSIF Level < 2.0 THEN
        Mode := 2;
    ELSE
        Mode := 0;
    END_IF
    
    CASE Mode OF
        0 : ValveOpen := FALSE; Alarm := FALSE;
        1 : ValveOpen := TRUE;  Alarm := TRUE;
        2 : ValveOpen := FALSE; Alarm := TRUE;
    END_CASE
END_FUNCTION_BLOCK
```
