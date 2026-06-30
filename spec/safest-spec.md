# SafeST — IEC 61131-3 Structured Text 安全子集规范

> **文档版本**：v1.1  
> **状态**：正式发布  
> **生效日期**：2026-06-30  
> **对应 Coq 文件**：`vstac/spec/safest.v`（形式化镜像）  
> **对应实现文件**：`vstac/src/lexer.v` `vstac/src/parser.v` `vstac/src/typechecker.v` `vstac/src/desugar.v`  

---

## 0. 文档控制

### 0.1 版本历史

| 版本 | 日期 | 变更说明 | 作者 |
|------|------|---------|------|
| v0.1 | 草案 | 初始草案 | — |
| v1.0 | 2026-06-29 | 正式发布。补充完整的 IEC 61131-3 子集定义及选择理由；完善类型提升规则（完整 10×10 矩阵）；新增形式化操作语义章节（小步语义）；补充完整示例集 | — |
| **v1.1** | **2026-06-30** | **新增 LINT(64位整数) 和 LREAL(64位浮点) 类型；新增带质量位的 Q 类型体系（QINT/QREAL/QLINT/QLREAL 等）；新增质量传播语义和影子内存设计；新增质量操作内置函数（Q_STATUS/Q_SET/Q_GOOD 等）；扩展类型提升矩阵至 12×12** | — |

### 0.2 约定

```
├─ 规则/约束编号格式：Sx.y（安全约束）、Tx.y（类型规则）、Lx.y（词法规则）
├─ EBNF 中 [...] 表示可选，{...} 表示重复零次或多次
├─ Coq 引用以 `vstac/spec/safest.v` 中的定义名为准
└─ 所有非规范性说明以"注："开头
```

---

## 1. 概述

SafeST 是 IEC 61131-3 国际标准中 Structured Text (ST) 语言的一个**安全关键子集**。本规范定义它的词法结构、语法、类型系统和安全约束。所有 SafeST 程序均可由 vstac 编译器编译为 SafeASM 字节码，且编译正确性已在 Coq 中形式化证明。

### 1.1 设计原则

1. **最小完备**：足够表达安全级仪控系统的全部控制逻辑需求（布尔逻辑、算术运算、定时器、计数器、PID、联锁、顺控等）
2. **静态安全**：所有资源分配在编译期完成——无动态内存分配、无指针/引用、无递归调用、所有循环有编译期可验证的上界
3. **可验证**：每个语法构造都有对应的 Coq 语义模型，可在形式化框架下进行推理证明
4. **确定终止**：所有循环（FOR/WHILE/REPEAT）都有编译期可确定的终止条件或最大迭代次数
5. **零运行时开销的安全检查**：数组边界检查、除零检查等由编译器在 SafeASM 中插入显式指令，而非依赖操作系统保护机制

---

## 2. IEC 61131-3 子集定义 (Subset Definition)

SafeST 是 IEC 61131-3 第三版（IEC 61131-3:2013）Structured Text 语言的一个**真子集**。本章系统地阐述哪些特性被纳入、哪些被排除，以及每项选择的工程与安全理由。

### 2.1 子集选择原则

| 原则 | 含义 | 影响范围 |
|------|------|---------|
| **P1: 安全关键适配** | 只包含安全级仪控系统中确实需要的语言特性 | 排除 SFC、动作、步进等 |
| **P2: 静态可决策性** | 所有属性必须在编译期可判定 | 排除动态内存、指针、递归、多态 |
| **P3: 形式化可建模** | 每个特性必须在 Coq 中有精确的语义模型 | 排除异常处理、运行时类型识别 |
| **P4: WCET 可计算** | 最差执行时间必须在编译期有界 | 排除非确定性循环、间接调用 |

### 2.2 逐项对比表

#### 数据类型

| IEC 61131-3 类型 | SafeST | 理由 |
|------------------|--------|------|
| BOOL | ✅ 包含 | 布尔逻辑最基础 |
| BYTE | ✅ 包含 | I/O 字节操作 |
| WORD | ✅ 包含 | 位操作、状态字 |
| DWORD | ✅ 包含 | 32 位状态字 |
| SINT (signed 8-bit) | ✅ 包含 | 小型计数器 |
| INT (signed 16-bit) | ✅ 包含 | 通用整数 |
| DINT (signed 32-bit) | ✅ 包含 | 主计数器/累加器 |
| LINT (signed 64-bit) | ✅ **v1.1 新增** | 高精度累加、64 位时间戳 |
| USINT/UINT/UDINT/ULINT | ❌ 排除 | 无符号类型可通过类型检查约束替代，减少类型复杂度 |
| USINT/UINT/UDINT/ULINT | ❌ 排除 | 无符号类型可通过类型检查约束替代，减少类型复杂度 |
| REAL (32-bit float) | ✅ 包含 | 模拟量处理（AI/AO） |
| LREAL (64-bit float) | ✅ **v1.1 新增** | 高精度模拟量、双精度中间计算 |
| TIME | ✅ 包含 | 定时器、超时逻辑必备 |
| DATE/TOD/DT | ❌ 排除 | 安全级逻辑无需绝对时间；由上层系统提供 |
| STRING/WSTRING | ❌ 排除 | 字符串处理涉及动态内存，违反 P2 |
| ARRAY | ✅ 部分 | **仅静态数组**（编译期固定边界），排除可变长度数组 `ARRAY[*]` |
| STRUCT | ❌ 排除 | 结构体嵌套增加内存布局复杂度，可以展开为扁平变量 |
| REF/REF_TO/POINTER | ❌ 排除 | 指针违反 P2（无法静态验证别名安全性） |
| ENUM | ❌ 排除 | 可用 `INT` + `CONSTANT` 替代，不损失安全性 |
| QUALITY | ✅ **v1.1 新增** | 信号质量码（GOOD/BAD/UNCERTAIN/NOT_CONNECTED） |
| Q* (QINT/QREAL 等) | ✅ **v1.1 新增** | 带质量位的变量类型，I/O 变量默认使用 |

#### 程序组织单元 (POU)

| IEC 61131-3 POU | SafeST | 理由 |
|-----------------|--------|------|
| PROGRAM | ✅ 包含 | 顶层程序入口 |
| FUNCTION | ✅ 包含 | 无状态计算（纯函数） |
| FUNCTION_BLOCK | ✅ 包含 | 有状态控制逻辑（定时器、计数器、PID 等） |
| METHOD | ❌ 排除 | 面向对象特性，安全级编程不需要，违反 P2 |
| PROPERTY | ❌ 排除 | 同上 |
| ACTION | ❌ 排除 | SFC 相关，安全级逻辑不需要 |
| TRANSITION | ❌ 排除 | SFC 相关 |
| STEP | ❌ 排除 | SFC 相关 |
| CLASS/INTERFACE | ❌ 排除 | OOP 特性，违反 P2 |

#### 语句

| IEC 61131-3 语句 | SafeST | 理由 |
|------------------|--------|------|
| 赋值 `:=` | ✅ 包含 | 核心语句 |
| IF/ELSIF/ELSE | ✅ 包含 | 条件分支 |
| CASE | ✅ 包含 | 多路分支 |
| FOR | ✅ 包含 | **限定上界为编译期常量**，见 S1 |
| WHILE | ✅ 包含 | **必须带 Loop Variant 注解**，见 S1 |
| REPEAT | ✅ 包含 | **必须带 Loop Variant 注解**，见 S1 |
| EXIT | ✅ 包含 | **仅允许在循环体内** |
| RETURN | ✅ 包含 | 提前返回 |
| FB 调用 | ✅ 包含 | 实例名+参数名绑定传参 |
| 函数调用 | ✅ 包含 | 按位置传参 |
| SFC 相关全部 | ❌ 排除 | 形式化语义复杂，WCET 难以确定 |
| JMP 标签 | ❌ 排除 | 无条件跳转破坏结构化编程 |
| `__NEW`/`__DELETE` | ❌ 排除 | 动态内存，违反 P2 |
| 异常处理 (TRY/CATCH) | ❌ 排除 | 违反 P3（异常的形式化模型复杂） |

#### 其他特性

| IEC 61131-3 特性 | SafeST | 理由 |
|------------------|--------|------|
| 直接地址访问 (`%I*`, `%Q*`) | ❌ 排除 | 用 IOMap Section 在 SafeASM 层处理 |
| 任务配置 (TASK) | ❌ 排除 | 由运行期 RTOS 层管理 |
| 重载 (OVERLOAD) | ❌ 排除 | 违反 P2（编译期名称解析复杂化） |
| 别名 (ALIAS) | ❌ 排除 | 增加别名分析的复杂性 |

### 2.3 与标准 ST 的差异汇总推论

SafeST 删除了约 **70%** 的 IEC 61131-3 ST 语言特性。保留的 30% 经过安全关键领域数十年的工程实践验证，足以表达：

- 联锁保护逻辑（布尔方程 + 定时器）
- 模拟量调节（PID + 算术运算）
- 顺控逻辑（状态机 + CASE）
- 定期扫描的数据采集（周期执行模型）

**工程验证**：附录 A 中的示例覆盖了上述四个领域的典型用例。

---

## 3. 词法规范 (Lexical Structure)

### 3.1 字符集

SafeST 源文件使用 **UTF-8 编码**（仅限 ASCII 子集用于关键字和标识符，字面量可使用 Unicode）。

### 3.2 关键字

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
QUALITY      GOOD         BAD          UNCERTAIN    NOT_CONNECTED
QBOOL        QBYTE        QWORD        QDWORD
QSINT        QINT         QDINT        QLINT
QREAL        QLREAL       QTIME
Q_STATUS     Q_SET        Q_VALUE      Q_WITH       Q_FORCE
Q_GOOD       Q_BAD        Q_UNCERTAIN
Q_NONE       Q_DISABLE
```

**显式排除的关键字**（标准 IEC 61131-3 中有但 SafeST 不支持的）：

```
STRING, WSTRING, REF, REF_TO, POINTER, ARRAY[*], __NEW, __DELETE,
METHOD, PROPERTY, INTERFACE, CLASS, ACTION, TRANSITION, STEP,
SFC 相关全部关键字
```

### 3.3 标识符

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

### 3.4 字面量

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

### 3.5 运算符

```
算术:      +  -  *  /  MOD
比较:      =  <>  <  >  <=  >=
逻辑:      AND  OR  XOR  NOT
赋值:      :=
其他:      ..  (范围运算符, CASE 中使用)
```

---

## 4. 语法规范 (Syntax / AST)

### 4.1 基本类型

```ebnf
<type> ::= BOOL
         | BYTE | WORD | DWORD
         | SINT | INT | DINT | LINT
         | REAL | LREAL
         | TIME
         | QUALITY
         | QBOOL | QBYTE | QWORD | QDWORD
         | QSINT | QINT | QDINT | QLINT
         | QREAL | QLREAL | QTIME
         | QARRAY '[' <low> '..' <high> ']' OF <qtype>
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
| **LINT** | **64** | **-2^63..2^63-1 (v1.1 新增)** |
| REAL | 32 | IEEE 754 单精度 |
| **LREAL** | **64** | **IEEE 754 双精度 (v1.1 新增)** |
| TIME | 64 | 纳秒计数，0..2^63-1 |
| **QUALITY** | **8** | **信号质量码 (v1.1 新增)** |

**带质量位的 Q 类型（v1.1 新增）**：每个普通类型对应一个带质量位的 Q 版本。

| Q 类型 | 值宽度 | 质量宽度 | 总内存占位 | 对齐到 |
|--------|--------|---------|-----------|-------|
| QBOOL | 1 B | 1 B | 4 B | 4 B |
| QBYTE | 1 B | 1 B | 4 B | 4 B |
| QWORD/QSINT | 2 B | 1 B | 4 B | 4 B |
| QDWORD/QINT | 4 B | 1 B | 8 B | 8 B |
| QDINT | 4 B | 1 B | 8 B | 8 B |
| QREAL | 4 B | 1 B | 8 B | 8 B |
| **QLINT** | **8 B** | **1 B** | **16 B** | **16 B** |
| **QLREAL** | **8 B** | **1 B** | **16 B** | **16 B** |
| QTIME | 8 B | 1 B | 16 B | 16 B |

**数组约束**：
- 仅支持**静态数组**（上下界为编译期常量）
- 最多 **3 维**
- 禁止可变长度数组

### 4.2 表达式 (Expressions)

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

### 4.3 语句 (Statements)

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

### 4.4 程序组织单元 (POU)

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

### 4.5 完整程序结构

```ebnf
<safe_st_program> ::= <global_var_decl_section>*
                      <pou>+
```

---

## 5. 类型系统 (Type System)

### 5.1 类型兼容性规则

#### 5.1.1 隐式提升方向

```
整数类型提升链：   SINT(8) → INT(16) → DINT(32) → LINT(64)
位串类型提升链：   BYTE(8) → WORD(16) → DWORD(32)
浮点类型提升链：   REAL(32) → LREAL(64)
布尔类型：         BOOL 独立，仅与 BOOL 兼容
时间类型：         TIME(64) 独立，仅与 TIME 兼容
数组类型：         要求维度、元素类型完全一致才兼容
质量类型：         QUALITY 独立，仅与 QUALITY 兼容
                   Q 类型提升规则与对应基础类型相同，质量透传
```

#### 5.1.2 完整 12×12 类型提升矩阵

下表给出任意两种类型 `T1`, `T2` 提升后的公共类型 `promote(T1, T2)`。空单元格表示类型不兼容（编译期报错）。

| T1 \\ T2 | BOOL | BYTE | WORD | DWORD | SINT | INT | DINT | **LINT** | REAL | **LREAL** | TIME | ARRAY |
|----------|------|------|------|-------|------|-----|------|---------|------|----------|------|-------|
| **BOOL** | BOOL | — | — | — | — | — | — | — | — | — | — | — |
| **BYTE** | — | BYTE | WORD | DWORD | — | — | — | — | — | — | — | — |
| **WORD** | — | WORD | WORD | DWORD | — | — | — | — | — | — | — | — |
| **DWORD** | — | DWORD | DWORD | DWORD | — | — | — | — | — | — | — | — |
| **SINT** | — | — | — | — | SINT | INT | DINT | **LINT** | — | — | — | — |
| **INT** | — | — | — | — | INT | INT | DINT | **LINT** | — | — | — | — |
| **DINT** | — | — | — | — | DINT | DINT | DINT | **LINT** | — | — | — | — |
| **LINT** | — | — | — | — | **LINT** | **LINT** | **LINT** | **LINT** | — | — | — | — |
| **REAL** | — | — | — | — | — | — | — | — | REAL | **LREAL** | — | — |
| **LREAL** | — | — | — | — | — | — | — | — | **LREAL** | **LREAL** | — | — |
| **TIME** | — | — | — | — | — | — | — | — | — | — | TIME | — |
| **ARRAY** | — | — | — | — | — | — | — | — | — | — | — | 见注¹ |

> **注¹**：数组兼容要求 `T_ARRAY(e1, l1, h1)` 与 `T_ARRAY(e2, l2, h2)` 满足 `e1 = e2 ∧ l1 = l2 ∧ h1 = h2`，即元素类型和维度完全一致。

#### 5.1.3 运算符有效类型

| 运算符 | 允许的操作数类型 | 结果类型 |
|--------|----------------|---------|
| `+`, `-`, `*` | INT/DINT/**LINT**/REAL/**LREAL** | 提升后类型 |
| `/` | INT/DINT/**LINT**/REAL/**LREAL** | 提升后类型 |
| `MOD` | INT/DINT/**LINT** | 提升后类型 |
| `=`, `<>` | 任意兼容类型对 | BOOL |
| `<`, `<=`, `>`, `>=` | INT/DINT/**LINT**/REAL/**LREAL**/BYTE/WORD/DWORD | BOOL |
| `AND`, `OR`, `XOR` | BOOL | BOOL |
| `NOT` | BOOL | BOOL |
| `-` (负号) | INT/DINT/**LINT**/REAL/**LREAL** | 同操作数类型 |
| `ABS` | INT/DINT/**LINT**/REAL/**LREAL** | 同操作数类型 |

### 5.2 带质量类型的兼容性规则

#### 5.2.1 质量值定义

质量码是 2 位编码，存储为 1 字节（低 2 位有效）：

| 质量常量 | 编码 | 含义 |
|---------|------|------|
| `GOOD` | 0b00 (0) | 信号正常，完全可信 |
| `UNCERTAIN` | 0b01 (1) | 质量降级，谨慎使用 |
| `BAD` | 0b10 (2) | 信号无效，禁止用于控制 |
| `NOT_CONNECTED` | 0b11 (3) | 信号源未连接 |

质量序关系：`GOOD < UNCERTAIN < BAD < NOT_CONNECTED`

#### 5.2.2 类型转换规则（含质量）

```
T → QT:     隐式允许，质量自动设为 GOOD
QT → T:     隐式允许（编译器发出 Q-STRIP 警告），质量信息丢弃
QT → QUALITY: 通过 Q_STATUS() 或隐式提取质量码
QUALITY → QT: 禁止（需要 Q_WITH(v, q) 构造器）
T → QUALITY: 禁止（普通类型无质量信息）
QT₁ → QT₂（提升/截断）: 质量透传
```

#### 5.2.3 质量传播规则

质量传播遵循 **worst() 函数**：

```
worst(GOOD, q) = q
worst(q, GOOD) = q
worst(UNCERTAIN, BAD) = BAD
worst(q1, q2) = q1  if q1 ≥ q2 （按质量序）
```

| 构造 | 质量传播规则 | 编号 |
|------|------------|------|
| 字面量 `42` | 质量 = GOOD | Q1 |
| 变量引用 `x` | 质量 = x.quality | Q2 |
| 一元运算 `-x`, `NOT x`, `ABS x` | 质量 = operand.quality | Q3 |
| 二元运算 `a + b` | 质量 = worst(a.quality, b.quality) | Q4 |
| 比较运算 `a > b` | 质量 = worst(a.quality, b.quality) | Q5 |
| AND/OR/XOR（逻辑） | 计算过的操作数 quality 的 worst | Q6 |
| 赋值 `x := e` | x.quality = e.quality | Q7 |
| 函数/FB 调用 | 结果质量 = worst(所有输入参数的质量) | Q8 |
| T → QT 隐式转换 | 质量设为 GOOD | Q9 |
| QT → T 显式（Q_VALUE） | 质量丢弃 | Q10 |

#### 5.2.4 赋值兼容性矩阵

```
目标 \ 来源    Plain(T)   Q(T)   QUALITY
─────────────────────────────────────────
Plain(T)       ✅         ⚠️①    ❌
Q(T)           ✅②       ✅     ❌
QUALITY        ❌        ✅③   ✅

① Q(T) → Plain(T): 隐式允许，发出 Q-STRIP 警告；可用 Q_VALUE() 消除
② Plain(T) → Q(T): 隐式允许，质量自动设为 GOOD
③ Q(T) → QUALITY: 通过 Q_STATUS() 提取
```

### 5.3 类型检查规则（语义）

类型检查规则采用**自然演绎 (Natural Deduction)** 格式：

```
  前提₁    前提₂    ...    前提ₙ
  ──────────────────────────────  (规则名)
        结  论
```

其中 `Γ` 是类型环境（变量名 → 类型），`Γ ⊢ e : T` 表示"在环境 Γ 下，表达式 e 的类型为 T"。

```
─────────────────────────────  (T_Literal)
Γ ⊢ literal : literal_type(literal)


Γ(x) = T
─────────────────────────────  (T_Var)
Γ ⊢ x : T


Γ ⊢ e₁ : T₁    Γ ⊢ e₂ : T₂    promote(T₁, T₂) = T₃    T₃ ∈ {INT, DINT, LINT, REAL, LREAL}
─────────────────────────────────────────────────────────────────────────────────────────  (T_Add)
Γ ⊢ e₁ + e₂ : T₃


Γ ⊢ e : T    T ∈ {BOOL, SINT, INT, DINT, LINT}
───────────────────────────────────────────────  (T_Neg)
Γ ⊢ -e : T


Γ ⊢ e : T    T ∈ {INT, DINT, LINT, REAL, LREAL}
───────────────────────────────────────────────  (T_ABS)
Γ ⊢ ABS e : T


Γ ⊢ e : T    T = BOOL
─────────────────────  (T_Not)
Γ ⊢ NOT e : T


Γ ⊢ e₁ : T₁    Γ ⊢ e₂ : T₂    comparable(T₁, T₂)
─────────────────────────────────────────────────  (T_Compare)
Γ ⊢ e₁ = e₂ : BOOL


Γ ⊢ e : BOOL
─────────────────────  (T_If)
Γ ⊢ IF e ... : OK


Γ ⊢ e : INT
─────────────────────  (T_Case)
Γ ⊢ CASE e ... : OK


Γ ⊢ e₁ : INT    Γ ⊢ e₂ : INT
─────────────────────────────  (T_For)
Γ ⊢ e₁ TO e₂ : INT


Γ ⊢ e : BOOL
─────────────────────  (T_While)
Γ ⊢ WHILE e ... : OK


Γ ⊢ e : BOOL
─────────────────────  (T_Repeat)
Γ ⊢ REPEAT ... UNTIL e : OK


Γ ⊢ x : T    Γ ⊢ e : T'    T' → T 可隐式转换
─────────────────────────────────────────────  (T_Assign)
Γ ⊢ x := e : OK


Γ ⊢ inst : FB_Type    params 类型匹配 FB 的 VAR_INPUT/VAR_IN_OUT
─────────────────────────────────────────────────────────────────  (T_FB_Call)
Γ ⊢ inst(params) : OK


--- v1.1 新增：Q 类型与质量检查规则 ---


Γ ⊢ e : T    T 是普通类型
─────────────────────────────  (T_Q_Inject)  T → QT，质量隐式 GOOD
Γ ⊢ e : Q(T)


Γ ⊢ e : Q(T)
─────────────────────────────  (T_Q_Extract)  QT → T，质量丢弃（警告）
Γ ⊢ Q_VALUE(e) : T


Γ ⊢ e : Q(T₁)    promote(T₁, T₂) = T₃
─────────────────────────────────────  (T_Q_Promote)  QT 间提升，质量透传
Γ ⊢ e : Q(T₃)


Γ ⊢ e : Q(T)
─────────────────────────────  (T_Q_Status)
Γ ⊢ Q_STATUS(e) : QUALITY


Γ ⊢ v : T    Γ ⊢ q : QUALITY
─────────────────────────────  (T_Q_With)
Γ ⊢ Q_WITH(v, q) : Q(T)


Γ ⊢ e : Q(T)
─────────────────────────────  (T_Q_Good)
Γ ⊢ Q_GOOD(e) : BOOL


Γ ⊢ e : Q(T)
─────────────────────────────  (T_Q_Bad)
Γ ⊢ Q_BAD(e) : BOOL


Γ ⊢ e : QUALITY
─────────────────────  (T_Quality_Literal)  GOOD/BAD/UNCERTAIN/NOT_CONNECTED
Γ ⊢ e : QUALITY
```

---

## 6. SafeST 操作语义 (Operational Semantics)

SafeST 的操作语义采用**小步语义 (small-step semantics)** 定义，与 Coq 文件 `vstac/spec/compiler_correctness.v` 中的形式化定义一致。

### 6.1 运行时状态

```
ST 运行时状态 σ = (vars, quality, pou_idx, stmt_idx, call_stack, cycle_cnt)
其中:
  vars:       list (ident × st_value)    所有变量的当前值
  quality:    list (ident × quality)     质量位置映射（v1.1 新增）
  pou_idx:    Z                          当前执行的 POU 索引
  stmt_idx:   Z                          当前语句索引
  call_stack: list Z                     调用栈（历史 POU 索引）
  cycle_cnt:  Z                          当前扫描周期的执行步数
```

### 6.2 运行时值

```
ST 运行时值 v ::= ST_V_BOOL(b)     b: bool
                | ST_V_BYTE(z)     z: 0..255
                | ST_V_WORD(z)     z: 0..65535
                | ST_V_DWORD(z)    z: 0..4294967295
                | ST_V_SINT(z)     z: -128..127
                | ST_V_INT(z)      z: -32768..32767
                | ST_V_DINT(z)     z: -2147483648..2147483647
                | ST_V_LINT(z)     z: -2^63..2^63-1 (v1.1)
                | ST_V_REAL(f)     f: float32
                | ST_V_LREAL(f)    f: float64 (v1.1)
                | ST_V_TIME(z)     z: 0..2^63-1 (纳秒)

ST 运行时质量 q ::= Q_GOOD | Q_UNCERTAIN | Q_BAD | Q_NOT_CONNECTED

带质量的值 (Q 类型) = (st_value, quality) 二元组
```

### 6.3 表达式求值规则（大步语义）

表达式求值为一个纯函数 `eval_expr(σ, e) → option (st_value × quality)`，无副作用。

```
-- 值求值规则（原始，不考虑质量）

eval_expr(σ, L_INT n)      = (ST_V_INT(n), GOOD)           (E_LitInt)
eval_expr(σ, L_REAL f)     = (ST_V_REAL(f), GOOD)          (E_LitReal)
eval_expr(σ, L_BOOL b)     = (ST_V_BOOL(b), GOOD)          (E_LitBool)
eval_expr(σ, L_TIME t)     = (ST_V_TIME(t), GOOD)          (E_LitTime)
eval_expr(σ, L_LINT n)     = (ST_V_LINT(n), GOOD)          (E_LitLInt)  (v1.1)
eval_expr(σ, L_LREAL f)    = (ST_V_LREAL(f), GOOD)         (E_LitLReal) (v1.1)

eval_expr(σ, E_VAR x)      = (lookup_var(σ.vars, x),
                               lookup_quality(σ.quality, x))  (E_Var)

eval_expr(σ, E_UNARY_OP U_NEG e1)
  = match eval_expr(σ, e1) with
    | (ST_V_INT(n),    q) => (ST_V_INT(-n),    q)
    | (ST_V_DINT(n),   q) => (ST_V_DINT(-n),   q)
    | (ST_V_LINT(n),   q) => (ST_V_LINT(-n),   q)        (v1.1)
    | (ST_V_REAL(f),   q) => (ST_V_REAL(PrimFloat.neg f), q)
    | (ST_V_LREAL(f),  q) => (ST_V_LREAL(PrimFloat.neg f), q)  (v1.1)
    | _              => None                             (E_Neg)

eval_expr(σ, E_UNARY_OP U_NOT e1)
  = match eval_expr(σ, e1) with
    | (ST_V_BOOL(b), q)   => (ST_V_BOOL(¬b), q)
    | _              => None                             (E_Not)

eval_expr(σ, E_BIN_OP B_ADD e1 e2)
  = match eval_expr(σ, e1), eval_expr(σ, e2) with
    | (ST_V_INT(n1),  q1),  (ST_V_INT(n2),  q2)
                           => (ST_V_INT(n1 + n2),  worst(q1, q2))
    | (ST_V_DINT(n1), q1), (ST_V_DINT(n2), q2)
                           => (ST_V_DINT(n1 + n2), worst(q1, q2))
    | (ST_V_LINT(n1), q1), (ST_V_LINT(n2), q2)
                           => (ST_V_LINT(n1 + n2), worst(q1, q2))   (v1.1)
    | (ST_V_REAL(f1), q1), (ST_V_REAL(f2), q2)
                           => (ST_V_REAL(f1 + f2), worst(q1, q2))
    | (ST_V_LREAL(f1), q1), (ST_V_LREAL(f2), q2)
                           => (ST_V_LREAL(f1 + f2), worst(q1, q2)) (v1.1)
    | (ST_V_INT(n1),  q1), (ST_V_DINT(n2), q2)
                           => (ST_V_DINT(n1 + n2), worst(q1, q2))
    | (ST_V_DINT(n1), q1), (ST_V_INT(n2),  q2)
                           => (ST_V_DINT(n1 + n2), worst(q1, q2))
    | (ST_V_DINT(n1), q1), (ST_V_LINT(n2), q2)
                           => (ST_V_LINT(n1 + n2), worst(q1, q2))   (v1.1)
    | (ST_V_LINT(n1), q1), (ST_V_DINT(n2), q2)
                           => (ST_V_LINT(n1 + n2), worst(q1, q2))   (v1.1)
    | (ST_V_REAL(f1), q1), (ST_V_LREAL(f2), q2)
                           => (ST_V_LREAL(f1 + f2), worst(q1, q2))  (v1.1)
    | (ST_V_LREAL(f1), q1), (ST_V_REAL(f2), q2)
                           => (ST_V_LREAL(f1 + f2), worst(q1, q2))  (v1.1)
    | _, _ => None                                     (E_Add)

eval_expr(σ, E_COMP C_EQ e1 e2)
  = match eval_expr(σ, e1), eval_expr(σ, e2) with
    | (ST_V_INT(n1),  q1), (ST_V_INT(n2),  q2)  => (ST_V_BOOL(n1 = n2), worst(q1, q2))
    | (ST_V_LINT(n1), q1), (ST_V_LINT(n2), q2)  => (ST_V_BOOL(n1 = n2), worst(q1, q2))   (v1.1)
    | (ST_V_REAL(f1), q1), (ST_V_REAL(f2), q2)  => (ST_V_BOOL(f1 = f2), worst(q1, q2))
    | (ST_V_LREAL(f1), q1), (ST_V_LREAL(f2), q2) => (ST_V_BOOL(f1 = f2), worst(q1, q2))  (v1.1)
    | (ST_V_BOOL(b1), q1), (ST_V_BOOL(b2), q2)  => (ST_V_BOOL(b1 ↔ b2), worst(q1, q2))
    | _, _ => None                                     (E_Eq)

eval_expr(σ, E_AND e1 e2)      -- 逻辑求值，带质量传播
  = match eval_expr(σ, e1) with
    | (ST_V_BOOL(false), q1) => (ST_V_BOOL(false), q1)    -- 逻辑，质量=e1
    | (ST_V_BOOL(true),  q1) => 
        match eval_expr(σ, e2) with
        | (ST_V_BOOL(b2), q2) => (ST_V_BOOL(b2), worst(q1, q2))
        | _ => None
        end
    | _ => None                                 (E_And)

eval_expr(σ, E_OR e1 e2)       -- 逻辑求值
  = match eval_expr(σ, e1) with
    | (ST_V_BOOL(true),  q1) => (ST_V_BOOL(true), q1)     -- 逻辑，质量=e1
    | (ST_V_BOOL(false), q1) =>
        match eval_expr(σ, e2) with
        | (ST_V_BOOL(b2), q2) => (ST_V_BOOL(b2), worst(q1, q2))
        | _ => None
        end
    | _ => None                                 (E_Or)

eval_expr(σ, E_XOR e1 e2)
  = match eval_expr(σ, e1), eval_expr(σ, e2) with
    | (ST_V_BOOL(b1), q1), (ST_V_BOOL(b2), q2) => (ST_V_BOOL(b1 ⊻ b2), worst(q1, q2))
    | _, _ => None                                 (E_Xor)

-- 质量辅助函数
worst(Q_GOOD, q)           = q
worst(q, Q_GOOD)           = q
worst(Q_UNCERTAIN, Q_BAD)  = Q_BAD
worst(Q_BAD, Q_UNCERTAIN)  = Q_BAD
worst(q1, q2)              = q1  如果 q1 ≥ q2 (按质量序)
```

### 6.4 语句小步语义

小步语义用 `step_st(p, σ) → σ'` 表示 ST 程序 p 从状态 σ 执行一步到 σ'。

```
-- 赋值语句
step_st(p, σ[S_ASSIGN x e])
  = σ[x := eval_expr(σ, e)]               (St_Assign)

-- IF-THEN-ELSE
step_st(p, σ[S_IF e then_blk else_blk])
  | eval_expr(σ, e) = ST_V_BOOL(true)  → enter_block(σ, then_blk)
  | eval_expr(σ, e) = ST_V_BOOL(false) → enter_block(σ, else_blk)
                                          (St_If)

-- CASE
step_st(p, σ[S_CASE e branches default])
  = match eval_expr(σ, e) with           (St_Case)
    | ST_V_INT(n)   → execute_case(σ, n, branches, default)
    | ST_V_DINT(n)  → execute_case(σ, n, branches, default)
    | _             → σ

-- FOR 循环
step_st(p, σ[S_FOR var start end step body])
  | 首次进入 → σ[var := eval_expr(σ, start)]  (St_For_Init)
  | 每次迭代后 → σ[var := σ(var) + step]       (St_For_Step)
  | 终止条件 → σ(var) > end → 跳出循环          (St_For_End)

-- WHILE 循环
step_st(p, σ[S_WHILE cond body])
  | eval_expr(σ, cond) = ST_V_BOOL(true)  → enter_block(σ, body)   (St_While_True)
  | eval_expr(σ, cond) = ST_V_BOOL(false) → 跳过循环               (St_While_False)

-- REPEAT 循环
step_st(p, σ[S_REPEAT body cond])
  | 首次进入 → enter_block(σ, body)                                (St_Repeat_Enter)
  | 每次循环后, eval_expr(σ, cond) = true  → 跳出                    (St_Repeat_Done)
  | 每次循环后, eval_expr(σ, cond) = false → 继续执行 body           (St_Repeat_Again)

-- 函数/FB 调用
step_st(p, σ[S_FB_CALL inst params])
  = execute_fb(σ, lookup_fb(p, inst), params)                       (St_FB_Call)

step_st(p, σ[E_FUNC_CALL f(args)])
  = push_call_frame(σ, f, args, body)                               (St_Func_Call)

-- RETURN
step_st(p, σ[S_RETURN])
  = pop_call_frame(σ)                                                (St_Return)

-- EXIT
step_st(p, σ[S_EXIT])
  = 跳出当前最内层循环                                               (St_Exit)
```

### 6.5 多步执行与终态

```
-- 多步执行的自反传递闭包
star_step_st(p, σ, σ')  :=  σ = σ'
                          |  ∃σ'', step_st(p, σ, σ'') ∧ star_step_st(p, σ'', σ')

-- 终态定义
terminal_state(σ) := σ.call_stack = nil
```

**注**：完整的形式化定义请参见 Coq 文件 `vstac/spec/compiler_correctness.v`。上述规则是其精确的数学表示。

---

## 7. 安全约束 (Safety Constraints)

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

## 8. 内置函数 (Built-in Functions)

SafeST 提供以下内置函数（在 Coq 中预先定义语义）：

| 函数 | 签名 | 说明 |
|------|------|------|
| `ABS` | `ANY_INT → ANY_INT` 或 `REAL/LREAL → REAL/LREAL` | 绝对值 |
| `SQRT` | `REAL/LREAL → REAL/LREAL` | 平方根 |
| `SIN` | `REAL/LREAL → REAL/LREAL` | 正弦 |
| `COS` | `REAL/LREAL → REAL/LREAL` | 余弦 |
| `MOVE` | `T → T` | 类型安全的值拷贝 |
| `SEL` | `BOOL, T, T → T` | 选择器 (SEL(g,a,b) = g?a:b) |
| `MUX` | `INT, T... → T` | 多路选择 |

### 8.1 质量操作内置函数（v1.1 新增）

| 函数 | 签名 | 说明 | WCET |
|------|------|------|------|
| `Q_STATUS(x)` | `QT → QUALITY` | 提取 Q 变量的质量码 | 3 条指令 ✅ |
| `Q_VALUE(x)` | `QT → T` | 提取 Q 变量的值部分，丢弃质量 | 1 条指令 ✅ |
| `Q_WITH(v, q)` | `(T, QUALITY) → QT` | 用值 v 和质量 q 构造 Q 值 | 4 条指令 ✅ |
| `Q_GOOD(x)` | `QT → BOOL` | 检查质量是否 GOOD | 4 条指令 ✅ |
| `Q_BAD(x)` | `QT → BOOL` | 检查质量是否 BAD | 4 条指令 ✅ |
| `Q_UNCERTAIN(x)` | `QT → BOOL` | 检查质量是否 UNCERTAIN | 4 条指令 ✅ |
| `Q_SET(x, q)` | `(QT, QUALITY) → void` | 强制设置 Q 变量的质量 | 3 条指令 ✅ |
| `Q_FORCE(x, v, q)` | `(QT, T, QUALITY) → void` | 强制设值 v 和质量 q | 7 条指令 ✅ |

所有质量函数的 WCET 均为固定指令数（无分支、无循环、无递归）。

### 8.2 质量常量

| 常量 | 编码值 | 含义 |
|------|--------|------|
| `GOOD` | 0 | 信号正常 |
| `UNCERTAIN` | 1 | 质量降级 |
| `BAD` | 2 | 信号无效 |
| `NOT_CONNECTED` | 3 | 信号未连接 |

### 8.3 类型转换函数（v1.1 新增，LINT/LREAL）

| 函数 | 签名 | 说明 |
|------|------|------|
| `LINT(v)` | `ANY_INT → LINT` | 整数提升到 LINT |
| `DINT(v)` | `LINT → DINT` | LINT 截断到 DINT |
| `LREAL(v)` | `REAL → LREAL` | 单精度提升到双精度 |
| `REAL(v)` | `LREAL → REAL` | 双精度截断到单精度 |
| `LINT(v)` | `REAL/LREAL → LINT` | 浮点截断到 LINT |
| `LREAL(v)` | `INT/DINT/LINT → LREAL` | 整数转换为双精度浮点 |

---

## 9. SafeST 语法限制总结

| 特性 | IEC 61131-3 ST | SafeST |
|------|---------------|--------|
| 数据类型 | 全部 + 用户自定义 | BOOL/BYTE/WORD/DWORD/SINT/INT/DINT/**LINT**/REAL/**LREAL**/TIME/**QUALITY**/ARRAY/**Q*** |
| 数组 | 静态+动态 | 仅静态（编译期固定边界） |
| 指针/引用 | REF, REF_TO, POINTER | ❌ 禁止 |
| 字符串 | STRING, WSTRING | ❌ 禁止 |
| **信号质量** | **无（IEC 61131-3 无内置质量位）** | **✅ Q* 类型体系 + 影子内存质量传播 (v1.1)** |
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

(* ================================================================
   示例 5: 函数调用 + 嵌套 IF (逻辑求值演示)
   
   ST 的 AND 是逻辑求值的 —— 当 x=0 时不会被零除
   ================================================================ *)
FUNCTION SafeDivide : REAL
    VAR_INPUT
        x : REAL;
        y : REAL;
    END_VAR
    VAR
        result : REAL := 0.0;
    END_VAR
    
    (* 逻辑求值: 当 x = 0.0 时，右操作数不计算，避免除零 *)
    IF (x <> 0.0) AND (result := y / x) > 0.0 THEN
        SafeDivide := result;
    ELSE
        SafeDivide := 0.0;
    END_IF
END_FUNCTION

PROGRAM CallDivide
    VAR_INPUT
        a : REAL := 10.0;
        b : REAL := 2.0;
    END_VAR
    VAR_OUTPUT
        out : REAL;
    END_VAR
    
    out := SafeDivide(a, b);
END_PROGRAM

(* ================================================================
   示例 6: WHILE 循环 (带 Loop Variant 注解)
   ================================================================ *)
PROGRAM GCD
    VAR_INPUT
        a : DINT := 48;
        b : DINT := 18;
    END_VAR
    VAR_OUTPUT
        result : DINT;
    END_VAR
    VAR
        x : DINT;
        y : DINT;
        tmp : DINT;
    END_VAR
    
    x := a;
    y := b;
    
    (* WHILE 循环: Loop Variant = y (严格递减，下界为 0) *)
    WHILE y <> 0 DO
        tmp := x MOD y;
        x := y;
        y := tmp;
    END_WHILE
    
    result := x;
END_PROGRAM

(* ================================================================
   示例 7: REPEAT 循环
   ================================================================ *)
FUNCTION_BLOCK Averager
    VAR_INPUT
        NewValue : INT;
        Reset    : BOOL;
    END_VAR
    VAR_OUTPUT
        Average : INT := 0;
        Count   : INT := 0;
    END_VAR
    VAR
        Sum : DINT := 0;
        Values : ARRAY[0..99] OF INT;
        idx : INT := 0;
    END_VAR
    
    IF Reset THEN
        Sum := 0;
        Count := 0;
        idx := 0;
        Average := 0;
    ELSE
        Values[idx] := NewValue;
        Sum := Sum + DINT(NewValue);
        Count := Count + 1;
        idx := idx + 1;
        
        (* REPEAT 循环: 至少执行一次 *)
        IF Count > 0 THEN
            Average := INT(Sum / DINT(Count));
        END_IF
    END_IF
    
    (* 循环直到填满缓冲区 *)
    REPEAT
        idx := 0;
    UNTIL idx < 100
    END_REPEAT
END_FUNCTION_BLOCK

(* ================================================================
   示例 8: FB 组合 (Timer + Counter 联锁逻辑)
   ================================================================ *)
FUNCTION_BLOCK InterlockLogic
    VAR_INPUT
        PressureHigh  : BOOL;
        FlowLow       : BOOL;
        ResetTrip     : BOOL;
    END_VAR
    VAR_OUTPUT
        TripRelay     : BOOL := FALSE;
        AlarmOutput   : BOOL := FALSE;
        TripCount     : INT := 0;
    END_VAR
    VAR
        (* 内部状态 *)
        Tripped       : BOOL := FALSE;
        TripTimer     : TIME := T#0ms;
        DebounceTimer : TIME := T#0ms;
        prev_PH       : BOOL := FALSE;
        prev_FL       : BOOL := FALSE;
    END_VAR
    
    (* 上升沿检测: PressureHigh *)
    IF PressureHigh AND NOT prev_PH THEN
        DebounceTimer := T#0ms;
    END_IF
    prev_PH := PressureHigh;
    
    (* 上升沿检测: FlowLow *)
    IF FlowLow AND NOT prev_FL THEN
        DebounceTimer := T#0ms;
    END_IF
    prev_FL := FlowLow;
    
    (* 防抖延时: 100ms 后确认跳机条件 *)
    IF (PressureHigh OR FlowLow) THEN
        IF DebounceTimer >= T#100ms THEN
            Tripped := TRUE;
        END_IF
        DebounceTimer := DebounceTimer + T#10ms;
    END_IF
    
    (* 跳机输出 *)
    TripRelay := Tripped;
    AlarmOutput := Tripped;
    
    (* 跳机计数 *)
    IF Tripped AND ResetTrip THEN
        TripCount := TripCount + 1;
        Tripped := FALSE;
        TripTimer := T#0ms;
    END_IF
    
    (* 跳机后保持: 直到 ResetTrip 至少 500ms *)
    IF Tripped THEN
        TripTimer := TripTimer + T#10ms;
    END_IF
END_FUNCTION_BLOCK

(* ================================================================
   示例 9: 数组边界 + 除零保护的编译期检查
   ================================================================ *)
PROGRAM SafeArrayAccess
    VAR
        Data   : ARRAY[0..15] OF INT;
        i      : INT := 0;
        sum    : INT := 0;
        avg    : INT := 0;
    END_VAR
    
    (* 编译期已知边界: i 从 0 到 15，数组访问安全 *)
    FOR i := 0 TO 15 DO
        sum := sum + Data[i];
    END_FOR
    
    (* 除零保护: 编译器插入零值检查 *)
    IF sum <> 0 THEN
        avg := 1000 / sum;
    ELSE
        avg := 0;
    END_IF
END_PROGRAM
```
