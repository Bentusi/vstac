# ST → SafeASM 语义保持转换说明

> **文档版本**：v0.1  
> **状态**：草案  
> **对应 Coq 文件**：`vstac/spec/compiler_correctness.v`  
> **目的**：让不熟悉 Coq 形式化方法的开发人员也能清晰理解 ST 语言的每种构造如何映射到 SafeASM 指令，以及为什么这种映射是正确的（语义保持）。

---

## 1. 核心原则

```
对于任意 ST 程序 P，如果 P 编译生成 SafeASM 模块 M，
那么 M 在 SafeASM 虚拟机上的执行行为，
与 P 在 ST 语义下的执行行为完全一致。
```

**通俗解释**：编译器不会改变程序的"意思"。你在 ST 中写了一个 `x := a + b`，在 SafeASM 中执行对应指令序列后，`x` 的值与 ST 语义规定的值完全一样。

---

## 2. 逐构造映射表 (ST → SafeASM)

这是开发人员最需要关心的核心文档。每种 ST 构造的编译映射都附带**语义保持理由**。

### 2.1 表达式映射

| ST 构造 | SafeASM 指令序列 | 语义保持理由 |
|---------|-----------------|-------------|
| **字面量** `42` | `I32_CONST 42` | 直接值映射，无歧义 |
| **布尔字面量** `TRUE` | `I32_CONST 1` | TRUE=1 映射 |
| **变量引用** `x` | `LOCAL_GET idx` | 编译期变量偏移已确定，运行期一致 |
| **数组访问** `arr[i]` | `[arr_base] [i] I32_ADD SAFE_BOUNDS_CHECK I32_LOAD` | 基址+偏移+边界检查 |
| **一元负号** `-x` | `[x] I32_CONST 0 SWAP I32_SUB` | 0 - x = -x |
| **逻辑非** `NOT x` | `[x] I32_EQZ` | NOT x == (x = 0) |
| **二元运算** `a + b` | `[a] [b] I32_ADD` | 值栈模型与表达式树同构 |
| **三元运算** `a * b + c` | `[a] [b] I32_MUL [c] I32_ADD` | 后序遍历，与 AST 一致 |
| **比较运算** `a > b` | `[a] [b] I32_GT_S` | 比较结果 0/1 直接入栈 |
| **短路 AND** `a AND b` | `[a] BR_IF 0 [b]` | a=false 时跳过 b 的计算 |
| **短路 OR** `a OR b` | `[a] BR_IF 1 [b]` | a=true 时跳过 b 的计算 |
| **XOR** `a XOR b` | `[a] [b] I32_XOR` | 直接位运算 |

### 2.2 语句映射

| ST 构造 | SafeASM 指令序列 | 语义保持理由 |
|---------|-----------------|-------------|
| **赋值** `x := e` | `[e] LOCAL_SET idx` | 先计算 e 的值压栈，再存入 x |
| **数组赋值** `a[i] := e` | `[base] [i] I32_ADD [e] I32_STORE` | 计算地址 → 存入值 |
| **IF-THEN** | `[cond] BR_IF end [then_body] end:` | cond=false 跳过 then 块 |
| **IF-THEN-ELSE** | `[cond] BR_IF else [then] BR end else: [else] end:` | 控制流分叉精确对应 |
| **CASE** | 级联 `BR_IF` 或 `BR_TABLE` | 每个分支对应一个基本块 |
| **FOR 循环** | `[init] SET i LOOP [body] [inc] [i<=end] BR_IF loop` | 循环结构一一映射 |
| **WHILE 循环** | `LOOP [cond] BR_IF end [body] BR loop end:` | 先判断再执行 |
| **REPEAT 循环** | `LOOP [body] [cond] BR_IF loop` | 先执行再判断 |
| **函数调用** `F(args)` | `[args] CALL func_idx` | 栈传递参数 + 返回值 |
| **FB 调用** `inst(a:=1)` | `[a] CALL fb_method_idx` | FB 数据在内存中，通过偏移访问 |
| **RETURN** | `RETURN` | 直接对应 |
| **EXIT** | `BR exit_depth` | 跳出当前循环 |

### 2.3 短路求值的精确保留

ST 的 `AND` 和 `OR` 是短路求值的（左操作数决定后，右操作数可能不计算）。

```
ST:  b := (x > 0) AND (y / x > 5)
     ── 当 x=0 时，右操作数 y/x 不会执行（避免除零）

SafeASM 映射:
  LOCAL_GET x        ; 加载 x
  I32_CONST 0
  I32_GT_S           ; x > 0 ?
  BR_IF false_br     ; 若 FALSE，跳过右侧计算，直接结果为 0
  LOCAL_GET y
  LOCAL_GET x
  I32_DIV_S          ; y / x (仅在 x>0 时执行)
  I32_CONST 5
  I32_GT_S           ; y/x > 5 ?
  BR end_br
false_br:
  I32_CONST 0        ; 结果为 FALSE
end_br:
  LOCAL_SET b        ; b := 结果
```

**语义保持**：ST 的短路语义与 BR_IF 跳转完全等价 ✅

---

## 3. 内存布局映射

### 3.1 变量到内存偏移

```
ST 变量声明                              SafeASM 线性内存偏移
─────────────────                      ─────────────────────
VAR_INPUT                               ← IO_INPUT_BASE
  AI1 : REAL;        ──►  offset 0-3
  DI1 : BOOL;        ──►  offset 4
END_VAR
                                        ← IO_OUTPUT_BASE
VAR_OUTPUT
  AO1 : REAL;        ──►  offset 0-3
  DO1 : BOOL;        ──►  offset 4
END_VAR
                                        ← GLOBAL_BASE
VAR_GLOBAL
  counter : DINT;    ──►  offset 0-3
  mode    : INT;     ──►  offset 4-5
END_VAR
                                        ← FB_BASE
FUNCTION_BLOCK Timer
  VAR_INPUT           ──►  Timer_inst 起始偏移
    Preset : TIME;                      offset 0-7
  END_VAR
    ...
END_FUNCTION_BLOCK
                                        ← STACK_BASE
(临时变量/函数调用栈)                    动态分配
                                        ← CONST_BASE
(常量池)                                固定偏移
```

### 3.2 偏移计算规则（编译期确定，运行期固定）

```
输入变量偏移(v) = IO_INPUT_BASE + input_layout(v_index)
输出变量偏移(v) = IO_OUTPUT_BASE + output_layout(v_index)
全局变量偏移(v) = GLOBAL_BASE + global_layout(v_index)
FB 字段偏移(inst, field) = FB_BASE + fb_base(inst) + field_offset(field)
局部变量偏移(f, idx) = STACK_BASE + frame_ptr(f) + idx × 4
```

**关键保证**：所有偏移在**编译期确定**，运行期固定。SafeASM 线性内存布局由 Memory Section 中的 `memory_segments` 描述。

---

## 4. 扫描周期映射

```
ST 扫描周期                         SafeASM 扫描周期
┌─────────────────┐               ┌──────────────────────────┐
│ 1. 读输入        │  ← I/O映射── │ 1. VM 将 I/O 输入拷贝到    │
│                  │              │    SafeASM 线性内存输入区  │
│ 2. 执行逻辑      │  ────►      │ 2. CALL entry_function   │
│                  │              │    (执行编译后的字节码)    │
│ 3. 写输出        │  ────►      │ 3. VM 将 SafeASM 线性内存  │
│                  │              │    输出区写回 I/O 输出     │
└─────────────────┘               └──────────────────────────┘
```

**关键保证**：一个 ST 扫描周期 = 一次 SafeASM `CALL entry_function` 调用，输入输出状态完全对齐。

---

## 5. 语义保持示例

### 例 1：简单表达式 `x := a + b * 2`

```
ST:  x := a + b * 2
      │
      ▼  解析树 (AST):
           :=
          /  \
         x    +
             / \
            a   *
               / \
              b   2
      │
      ▼  编译为 SafeASM (后序遍历):
      LOCAL_GET a_idx    ; 加载 a 的值到栈
      LOCAL_GET b_idx    ; 加载 b 的值到栈
      I32_CONST 2        ; 加载常量 2
      I32_MUL            ; 计算 b * 2，结果在栈顶
      I32_ADD            ; 计算 a + (b*2)，结果在栈顶
      LOCAL_SET x_idx    ; 将栈顶值存入 x
      
      │
      ▼  ST 语义: x = [[a]] + ([[b]] × 2)
      ▼  ASM 语义: 栈计算结果与 ST 语义一致 ✅
```

**为什么正确**：表达式树的后序遍历天然对应值栈操作——左子树先入栈，右子树后入栈，根节点运算消耗栈顶元素。这是编译原理中经过形式化证明的经典结论。

### 例 2：IF 条件分支

```
ST:  IF a > b THEN max := a ELSE max := b END_IF
      │
      ▼  编译为 SafeASM:
      LOCAL_GET a_idx    ; 加载 a
      LOCAL_GET b_idx    ; 加载 b
      I32_GT_S           ; 比较 a > b → 栈顶为 0 或 1
      BR_IF else_br      ; 如果 0 (a<=b) 跳转到 else
      LOCAL_GET a_idx    ; then 分支: 加载 a
      LOCAL_SET max_idx  ; max := a
      BR end_br
  else_br:
      LOCAL_GET b_idx    ; else 分支: 加载 b
      LOCAL_SET max_idx  ; max := b
  end_br:
      
      │
      ▼  语义保持: ST 的 IF 语义 = ASM 的分支跳转语义
         IF 条件成立 → 执行 then 块 → 跳过 else
         IF 条件不成立 → 跳过 then → 执行 else 块
         两条路径的计算结果等价 ✅
```

### 例 3：FOR 循环

```
ST:  FOR i := 1 TO 10 DO total := total + i END_FOR
      │
      ▼  编译为 SafeASM:
      I32_CONST 1
      LOCAL_SET i_idx    ; i := 1
  loop_start:
      LOCAL_GET i_idx    ; 加载 i
      I32_CONST 10
      I32_GT_S           ; i > 10 ?
      BR_IF loop_end     ; 是 → 跳出
      LOCAL_GET total_idx
      LOCAL_GET i_idx
      I32_ADD
      LOCAL_SET total_idx ; total := total + i
      LOCAL_GET i_idx
      I32_CONST 1
      I32_ADD
      LOCAL_SET i_idx    ; i := i + 1
      BR loop_start      ; 继续循环
  loop_end:
      
      │
      ▼  语义保持:
         ST: for i=1 to 10 → total = total + i
         ASM: LOOP + BR_IF → 完全相同的迭代语义 ✅
         循环次数 = 10，编译期已知 ✅ (安全约束满足)
```

### 例 4：函数调用

```
ST:  result := Add(5, 3)
     
     FUNCTION Add : INT
         VAR_INPUT a, b : INT; END_VAR
         Add := a + b;
     END_FUNCTION
      │
      ▼  编译为 SafeASM:
      I32_CONST 5        ; 参数 1
      I32_CONST 3        ; 参数 2
      CALL 0             ; 调用函数索引 0 (Add)
      LOCAL_SET result_idx  ; 将返回值存入 result
      
  ; Add 函数的 SafeASM:
  ; Type: [I32, I32] → [I32]
  ; Code:
  func_Add:
      LOCAL_GET 0        ; 加载参数 a
      LOCAL_GET 1        ; 加载参数 b
      I32_ADD            ; a + b
      RETURN             ; 返回栈顶值
      
      │
      ▼  语义保持:
         ST 语义: result = Add(5, 3) = 5 + 3 = 8
         ASM 语义: CALL 0 → 执行 Add 指令 → RETURN → 栈顶=8
         参数传递和返回值一一对应 ✅
```

---

## 6. 编译正确性形式化定理（开发人员注解版）

以下为 Coq 中声明的核心定理，附带通俗解释。

### 6.1 抽象关系 R

```
R(st_state, asm_state) 定义为:
  ─────────────────────────────────────
  1. 每个 ST 变量的值 = SafeASM 内存中对应偏移处的值
     例: st.x = 42 → mem[GLOBAL_BASE + x_offset] = 42
     
  2. 当前执行位置对应
     例: ST 执行到第 5 行 → ASM 的 pc 指向第 5 行对应的指令
     
  3. 变量类型兼容
     ST 的 INT = ASM 的 I32
     ST 的 REAL = ASM 的 F32
     ...
```

### 6.2 编译正确性定理

```
定理 semantics_preservation:
  如果 [ST 程序 P 编译成功生成 SafeASM 模块 M]
  且 [ST 状态 s1 执行一步到 s2]
  且 [s1 与 ASM 状态 t1 满足抽象关系 R]
  那么 [ASM 状态 t1 执行若干步到 t2]
  且 [s2 与 t2 仍然满足抽象关系 R]

形象理解:
    ST 世界:        s1 ──一步──→ s2
                    │              │
   R 关系 (对齐)     │              │
                    ▼              ▼
   ASM 世界:       t1 ──多步──→ t2
    
   不管 ST 中怎么跳，ASM 总能"跟上"并保持状态一致。
   编译没有改变程序的语义。这叫作 Simulation Relation。
```

### 6.3 安全保持定理

```
定理 safety_preservation:
  如果 [ST 程序 P 编译成功]
  且 [P 通过了类型检查]
  那么 [编译产物 M 满足所有安全约束]:
    ✓ 循环上限已确定
    ✓ 所有内存访问在声明范围内
    ✓ 周期指令数有限
    ✓ 函数无递归调用
    
  通俗理解: 编译器不仅是正确的，还是安全的。
  它保证输出的 SafeASM 代码满足安全约束。
```

---

## 7. 验证检查清单

对于每个 ST 构造，开发人员应验证以下语义保持条件：

| 检查项 | 说明 |
|--------|------|
| ✅ 值一致性 | 编译前后的变量值相同 |
| ✅ 控制流一致性 | 分支/循环的执行路径相同 |
| ✅ 类型一致性 | 类型转换符合规范 |
| ✅ 副作用一致性 | 函数/FB 的副作用（输出变量修改）一致 |
| ✅ 终止性 | 有限循环在有限步内终止 |
| ✅ 错误处理 | 除零/越界等错误触发方式一致 |

---

## 附录 A：常见问题

**Q: 为什么值栈模型能保证语义正确？**
A: 表达式树的后序遍历与值栈操作同构——这是编译器理论中已被广泛证明的结论。每个子表达式的结果压入栈，父运算消耗栈顶元素，最终的栈顶值就是整个表达式的结果。

**Q: 循环的语义保持如何保证？**
A: FOR 循环的语义保持通过 LOOP/BR_IF/BR 的组合实现。LOOP 标记循环开始，条件判断决定是否继续，BR 跳回循环开始。这与 ST 的 FOR 语义（初始化→判断→执行→增量→判断→...）完全对应。

**Q: 如果 SafeASM 解释器有 bug 怎么办？**
A: 编译正确性定理只保证"如果 VM 正确执行 SafeASM 指令，则结果与 ST 语义一致"。VM 本身的正确性需要通过 C 语言级别的测试和（可选）形式化验证来保证。这就是为什么我们将编译器证明和 VM 分开——编译器证明用 Coq，VM 正确性用测试。

**Q: 函数调用怎么保证语义保持？**
A: 通过 CALL/RETURN 指令机制和栈帧管理。参数在调用前压入值栈，CALL 指令创建新栈帧，RETURN 返回值留在栈顶，恢复调用者帧。这与 ST 的函数调用语义（传参→执行→返回）完全对应。
