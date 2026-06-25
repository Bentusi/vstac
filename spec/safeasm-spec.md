# SafeASM — 安全汇编字节码规范

> **文档版本**：v0.1  
> **状态**：草案  
> **对应 Coq 文件**：`vstac/spec/safeasm.v`  
> **编码方式**：固定宽度编码（非 LEB128）  

---

## 1. 概述

SafeASM 是一种自定义安全汇编字节码格式，作为 **vestac 编译器** 的输出目标和 **C 语言 SafeASM 虚拟机** 的输入。它基于 WASM 核心指令集做安全化剪裁和扩展，采用**固定宽度编码**以确保 WCET 确定性和形式化验证的可追溯性。

### 1.1 设计原则

1. **固定宽度编码** — 所有立即数/索引固定 4 字节（i32）或 8 字节（i64/f64），无变长编码
2. **确定性执行** — 禁止 `memory.grow`、`call_indirect` 等非确定性指令
3. **安全元数据内置** — 二进制中包含 Safety/IOMap/WCET 等安全扩展段
4. **可验证格式** — 每个 `.sasm` 文件的 CRC32 校验和覆盖除 Magic 外的所有字节

---

## 2. 二进制格式总览

```
┌──────────────────────────────────────────────────────┐
│  SafeASM Binary Format (.sasm)                        │
├──────────────────────────────────────────────────────┤
│  [Magic]      "SASM"       固定 4 字节 (0x4D534153, 小端序存储 "SASM")  │
│  [Version]    uint8        当前版本 = 0x01           │
│  [Flags]      uint8        安全等级 + 特性位图        │
├──────────────────────────────────────────────────────┤
│  [Section Header] 每个段前有 8 字节头:                │
│    - type:   uint8  (段类型)                         │
│    - length: uint32 (段长度, 固定 4 字节)            │
│    - flags:  uint8  (段属性)                         │
├──────────────────────────────────────────────────────┤
│  Section 0: Type Section     (函数签名)               │
│  Section 1: Function Section (函数定义)               │
│  Section 2: Memory Section   (内存布局声明)           │
│  Section 3: IOMap Section    (I/O 映射表)             │
│  Section 4: Code Section     (字节码)                 │
│  Section 5: Safety Section   (安全注解)               │
│  Section 6: WCET Section     (WCET 分析信息)          │
│  Section 7: Debug Section    (可选调试符号)            │
├──────────────────────────────────────────────────────┤
│  [Checksum]   CRC32         4 字节，覆盖 Magic 后所有字节 │
└──────────────────────────────────────────────────────┘
```

### 2.1 固定宽度编码规则

| 数据类型 | 编码规则 |
|---------|---------|
| `uint8` | 1 字节，直接存储 |
| `uint32` | 4 字节，小端序 |
| `sint32` | 4 字节，小端序，二进制补码 |
| `uint64` | 8 字节，小端序 |
| `float32` | 4 字节，IEEE 754 单精度 |
| `float64` | 8 字节，IEEE 754 双精度 |

### 2.2 Section 头格式

每个段之前都有一个 8 字节的段头：

```
段头结构 (8 字节):
  [0]    type:   uint8   段类型
  [1-4]  length: uint32  段数据长度（不含段头）
  [5]    reserved: uint8 保留位
  [6-7]  flags:  uint16  段属性位图
```

段类型枚举：

| 值 | 段名 | 必选 | 说明 |
|----|------|------|------|
| 0 | TYPE | 是 | 函数类型签名 |
| 1 | FUNC | 是 | 函数声明 |
| 2 | MEM | 是 | 线性内存布局 |
| 3 | IOMAP | 是 | I/O 映射表 |
| 4 | CODE | 是 | 字节码 |
| 5 | SAFE | 是 | 安全注解 |
| 6 | WCET | 否 | WCET 分析信息 |
| 7 | DEBUG | 否 | 调试符号 |

---

## 3. 指令集 (Instruction Set)

### 3.1 指令编码格式

每条指令由 **1 字节操作码 (opcode)** 后跟 **固定宽度的立即数**（如果有）组成。

```
指令编码:
  [0]     opcode:    uint8    1 字节操作码
  [1..N]  immediates: 固定宽度  取决于指令类型
```

### 3.2 指令列表

#### 控制流指令

| 操作码 | 指令 | 立即数 | 栈效果 | 说明 |
|--------|------|--------|--------|------|
| 0x00 | `UNREACHABLE` | 无 | - | 不可达指令（触发安全陷阱） |
| 0x01 | `NOP` | 无 | - | 空操作 |
| 0x02 | `BLOCK` | `len:uint32` | - | 块开始，len 为块内指令字节数 |
| 0x03 | `LOOP` | `len:uint32` | - | 循环块开始 |
| 0x04 | `BR` | `depth:uint32` | - | 无条件跳转到 depth 层外的 block/loop |
| 0x05 | `BR_IF` | `depth:uint32` | `i32 cond → -` | 条件跳转（cond ≠ 0 时跳转） |
| 0x06 | `RETURN` | 无 | - | 从当前函数返回 |

#### 函数调用

| 操作码 | 指令 | 立即数 | 栈效果 | 说明 |
|--------|------|--------|--------|------|
| 0x10 | `CALL` | `idx:uint32` | `args... → results...` | 直接调用函数 idx |

#### 参数栈操作

| 操作码 | 指令 | 立即数 | 栈效果 | 说明 |
|--------|------|--------|--------|------|
| 0x1A | `DROP` | 无 | `v → -` | 丢弃栈顶值 |
| 0x1B | `SELECT` | 无 | `c v1 v2 → v` | 三目选择: v = c ? v1 : v2 |
| 0x20 | `LOCAL_GET` | `idx:uint32` | `→ v` | 读取局部变量 idx |
| 0x21 | `LOCAL_SET` | `idx:uint32` | `v → -` | 写入局部变量 idx |
| 0x22 | `LOCAL_TEE` | `idx:uint32` | `v → v` | 写入局部变量但保留值在栈上 |

#### i32 常量加载

| 操作码 | 指令 | 立即数 | 栈效果 |
|--------|------|--------|--------|
| 0x41 | `I32_CONST` | `val:sint32` | `→ i32` |

#### i32 比较运算

| 操作码 | 指令 | 栈效果 | 说明 |
|--------|------|--------|------|
| 0x45 | `I32_EQZ` | `i32 → i32` | 等零判断 |
| 0x46 | `I32_EQ` | `i32 i32 → i32` | 相等 |
| 0x47 | `I32_NE` | `i32 i32 → i32` | 不等 |
| 0x48 | `I32_LT_S` | `i32 i32 → i32` | 有符号小于 |
| 0x49 | `I32_LE_S` | `i32 i32 → i32` | 有符号小于等于 |
| 0x4A | `I32_GT_S` | `i32 i32 → i32` | 有符号大于 |
| 0x4B | `I32_GE_S` | `i32 i32 → i32` | 有符号大于等于 |

#### i32 算术运算

| 操作码 | 指令 | 栈效果 | 说明 |
|--------|------|--------|------|
| 0x6A | `I32_ADD` | `i32 i32 → i32` | 加法 |
| 0x6B | `I32_SUB` | `i32 i32 → i32` | 减法 |
| 0x6C | `I32_MUL` | `i32 i32 → i32` | 乘法 |
| 0x6D | `I32_DIV_S` | `i32 i32 → i32` | 有符号除法（零除触发陷阱） |
| 0x6F | `I32_REM_S` | `i32 i32 → i32` | 有符号取模 |

#### i32 位运算

| 操作码 | 指令 | 栈效果 |
|--------|------|--------|
| 0x71 | `I32_AND` | `i32 i32 → i32` |
| 0x72 | `I32_OR` | `i32 i32 → i32` |
| 0x73 | `I32_XOR` | `i32 i32 → i32` |
| 0x74 | `I32_SHL` | `i32 i32 → i32` |
| 0x75 | `I32_SHR_S` | `i32 i32 → i32` |
| 0x76 | `I32_ROTL` | `i32 i32 → i32` |
| 0x77 | `I32_ROTR` | `i32 i32 → i32` |

#### i64 指令（扩展）

| 操作码 | 指令 | 说明 |
|--------|------|------|
| 0x50 | `I64_CONST` | `val:sint64 → i64` |
| 0x53 | `I64_EQZ` | 等零判断 |
| 0x54-0x5B | `I64_EQ/NE/LT_S/LE_S/GT_S/GE_S` | 比较运算 |
| 0x7C-0x7E | `I64_ADD/SUB/MUL` | 算术运算 |
| 0x7F-0x80 | `I64_DIV_S/REM_S` | 除法/取模 |

#### 浮点指令

| 操作码 | 指令 | 说明 |
|--------|------|------|
| 0x43 | `F32_CONST` | `val:float32 → f32` |
| 0x44 | `F64_CONST` | `val:float64 → f64` |
| 0x92-0x97 | `F32_ADD/SUB/MUL/DIV` | f32 算术 |
| 0x9A-0x9F | `F32_EQ/NE/LT/LE/GT/GE` | f32 比较 |
| 0xA0 | `F32_ABS` | f32 绝对值 |
| 0xA1 | `F32_NEG` | f32 取反 |
| 0xA2 | `F32_SQRT` | f32 平方根 |
| 0xA3-0xA8 | `F64_ADD/SUB/MUL/DIV` | f64 算术 |
| 0xAA-0xAF | `F64_EQ/NE/LT/LE/GT/GE` | f64 比较 |

#### 类型转换

| 操作码 | 指令 | 说明 |
|--------|------|------|
| 0xA7 | `I32_WRAP_I64` | i64 → i32 截断 |
| 0xAE | `I64_EXTEND_I32_S` | i32 → i64 符号扩展 |
| 0xAF | `I32_TRUNC_F32_S` | f32 → i32 截断 |
| 0xB0 | `I32_TRUNC_F64_S` | f64 → i32 截断 |
| 0xB7 | `F32_CONVERT_I32_S` | i32 → f32 转换 |
| 0xBB | `F64_CONVERT_I32_S` | i32 → f64 转换 |

#### 内存操作

所有内存操作附带固定宽度的内存参数：

```
memory_arg (4 字节):
  [0-1]  align:    uint16   对齐要求 (log2)
  [2-3]  offset:   uint16   基址偏移
```

| 操作码 | 指令 | 参数 | 栈效果 | 说明 |
|--------|------|------|--------|------|
| 0x28 | `I32_LOAD` | `memory_arg` | `addr:i32 → val:i32` | 加载 i32 |
| 0x29 | `I64_LOAD` | `memory_arg` | `addr:i32 → val:i64` | 加载 i64 |
| 0x2A | `F32_LOAD` | `memory_arg` | `addr:i32 → val:f32` | 加载 f32 |
| 0x2B | `F64_LOAD` | `memory_arg` | `addr:i32 → val:f64` | 加载 f64 |
| 0x36 | `I32_STORE` | `memory_arg` | `addr:i32 val:i32 → -` | 存储 i32 |
| 0x37 | `I64_STORE` | `memory_arg` | `addr:i32 val:i64 → -` | 存储 i64 |
| 0x38 | `F32_STORE` | `memory_arg` | `addr:i32 val:f32 → -` | 存储 f32 |
| 0x39 | `F64_STORE` | `memory_arg` | `addr:i32 val:f64 → -` | 存储 f64 |

#### 安全扩展指令

| 操作码 | 指令 | 参数 | 说明 |
|--------|------|------|------|
| 0xFC | `SAFE_ASSERT` | `assert_type:uint8 data...` | 安全断言，VM 运行时检查 |
| 0xFD | `SAFE_BOUNDS_CHECK` | `low:uint32 high:uint32` | 显式边界检查 |

`SAFE_ASSERT` 类型：

| assert_type | 数据 | 说明 |
|------------|------|------|
| 0 | `limit:uint32` | 周期指令数上限 |
| 1 | `depth:uint32` | 栈深度上限 |
| 2 | `low:uint32 high:uint32` | 内存访问范围 |

---

## 4. 各段详细格式

### 4.0 文件头 (Header)

```
[0-3]    magic:   4 字节 = 0x4D534153 ("SASM" 小端序)
[4]      version: uint8 = 0x01
[5]      flags:   uint8
         bit 0: 安全等级 (0=SIL2, 1=SIL3)
         bit 1: 热备支持 (0=不支持, 1=支持)
         bits 2-7: 保留
```

### 4.1 Type Section (段类型 0)

每个函数类型签名定义：

```
每个函数类型:
  [0]      param_count: uint32
  [1..]    param_types: param_count × uint8
  [n+1]    return_count: uint32  (0 或 1)
  [n+2..]  return_types: return_count × uint8

值类型编码:
  0x7F = I32
  0x7E = I64
  0x7D = F32
  0x7C = F64
```

### 4.2 Function Section (段类型 1)

```
每个函数声明:
  [0-3]    type_idx:  uint32  对应 Type Section 中的索引
  [4-7]    local_count: uint32  局部变量数量
  [8..]    local_types: local_count × uint8  局部变量类型
```

### 4.3 Memory Section (段类型 2)

```
总内存声明:
  [0-3]    total_size: uint32  线性内存总大小 (固定，编译期确定)
  [4-7]    segment_count: uint32  内存段数量

每个内存段:
  [0]      segment_type: uint8
           0 = IO_INPUT    (I/O 输入区，只读)
           1 = IO_OUTPUT   (I/O 输出区，可写)
           2 = GLOBAL      (全局变量区)
           3 = FB_DATA     (FB 实例数据区)
           4 = STACK       (栈区)
           5 = CONST       (常量区)
  [1-4]    start_offset: uint32  基址
  [5-8]    size:         uint32  大小
```

### 4.4 IOMap Section (段类型 3)

```
每个 I/O 映射条目:
  [0-3]    st_var_name_offset: uint32  变量名字符串在 Debug Section 的偏移
  [4-7]    mem_offset:   uint32  在 SafeASM 线性内存中的偏移
  [8-11]   channel_id:   uint32  物理通道 ID
  [12]     direction:    uint8   0=INPUT, 1=OUTPUT
  [13]     io_type:      uint8   0=AI, 1=AO, 2=DI, 3=DO
  [14-17]  bit_width:    uint32  位宽
  [18-25]  scale_factor: float64  工程量转换系数
  [26-33]  bias:         float64  偏移量
  [34-37]  safety_limit_low:  sint32  安全下限
  [38-41]  safety_limit_high: sint32  安全上限
```

### 4.5 Code Section (段类型 4)

```
每个函数的代码体:
  [0-3]    func_idx: uint32  对应的 Function 索引
  [4-7]    body_size: uint32  代码体字节数
  [8..]    body: byte[body_size]  指令序列

代码段 = 函数代码体的列表
```

### 4.6 Safety Section (段类型 5)

```
安全注解:
  [0]      safety_level: uint8  安全等级
  [1-4]    cycle_limit:  uint32  每周期最大指令数
  [5-8]    global_stack_depth: uint32  全局栈深度上限

循环上限表:
  [9-12]   loop_count: uint32  循环上限条目数
  每个条目:
    [0-3]  func_idx:   uint32  所属函数索引
    [4-7]  instr_offset: uint32  循环开始指令偏移
    [8-11] max_iterations: uint32  最大迭代次数

内存访问范围表:
  每个条目:
    [0-3]  low:  uint32  范围下限
    [4-7]  high: uint32  范围上限
```

### 4.7 WCET Section (段类型 6, 可选)

```
WCET 信息:
  [0-3]    func_count: uint32
  每个函数:
    [0-3]  func_idx:   uint32
    [4-7]  wcet_cycles: uint32  最差执行周期数
    [8-11] wcet_ns:     uint32  最差执行时间 (ns)
```

### 4.8 Debug Section (段类型 7, 可选)

```
调试符号表:
  [0-3]    string_count: uint32
  每个字符串:
    [0-3]  len:  uint32  字符串长度
    [4..]  data: byte[len]  UTF-8 字符串
```

---

## 5. SafeASM 执行语义

### 5.1 运行时状态

```
运行时状态:
  ┌─────────────────────┐
  │ 值栈 (value stack)   │  ← 操作数栈，LIFO
  ├─────────────────────┤
  │ 调用帧栈 (frame stack)│  ← 函数调用栈
  │ ┌─────────────────┐ │
  │ │ Frame            │ │
  │ │  - locals[]      │ │  ← 局部变量数组
  │ │  - func_idx      │ │  ← 当前函数索引
  │ │  - pc            │ │  ← 程序计数器
  │ └─────────────────┘ │
  ├─────────────────────┤
  │ 线性内存              │  ← byte[]，固定大小
  ├─────────────────────┤
  │ 全局变量              │  ← value[]，固定数量
  ├─────────────────────┤
  │ 周期计数器            │  ← 当前周期已执行指令数
  └─────────────────────┘
```

### 5.2 核心执行规则

```
每条指令执行:
  1. 从当前帧的 pc 位置读取 opcode
  2. 解码指令和立即数
  3. 检查预条件（栈深度、类型匹配）
  4. 执行指令（修改栈/内存/帧）
  5. pc += 指令长度
  6. cycle_cnt += 1
  7. 若 cycle_cnt > cycle_limit → 触发安全陷阱
```

### 5.3 函数调用规则

```
CALL idx:
  1. 从函数表中查找 func_idx = idx 的函数
  2. 从当前值栈弹出参数
  3. 创建新帧:
     - locals = 参数 + 局部变量默认值
     - func_idx = idx
     - pc = 该函数的 code 起始位置
  4. 新帧压入帧栈
  5. 开始执行新帧

RETURN:
  1. 当前帧的返回值（若有）留在值栈
  2. 弹出当前帧
  3. 恢复上一帧的 pc（调用后的下一条指令）
```

### 5.4 安全约束

```
每个 step 前检查:
  1. cycle_cnt < cycle_limit  (周期指令数上限)
  2. stack_depth(帧栈) ≤ global_stack_depth (调用栈深度)
  3. 值栈深度 ≤ MAX_VALUE_STACK_DEPTH
  4. 所有 LOAD/STORE 地址在 mem_access_map 范围内
  5. 除法指令除数 ≠ 0
```

---

## 6. 安全指令示例

### 6.1 简单加法

```
原始 ST:  x := a + b

编译为 SafeASM:
  41 00 00 00 0A     I32_CONST 10         ; 加载 a=10
  41 00 00 00 14     I32_CONST 20         ; 加载 b=20
  6A                 I32_ADD              ; 加法
  21 00 00 00 00     LOCAL_SET 0          ; 存入 x(局部变量0)
```

### 6.2 IF-ELSE

```
原始 ST:  IF a > b THEN max := a ELSE max := b END_IF

编译为 SafeASM:
  20 00 00 00 00     LOCAL_GET 0          ; 加载 a
  20 00 00 00 01     LOCAL_GET 1          ; 加载 b
  4A                 I32_GT_S             ; a > b ?
  05 00 00 00 02     BR_IF 2              ; 不成立则跳过 then
  20 00 00 00 00     LOCAL_GET 0          ; then: 加载 a
  21 00 00 00 02     LOCAL_SET 2          ; max := a
  04 00 00 00 01     BR 1                 ; 跳过 else
  20 00 00 00 01     LOCAL_GET 1          ; else: 加载 b
  21 00 00 00 02     LOCAL_SET 2          ; max := b
```

### 6.3 FOR 循环

```
原始 ST:  FOR i := 1 TO 10 DO sum := sum + i END_FOR

编译为 SafeASM:
  41 00 00 00 01     I32_CONST 1          ; i = 1
  21 00 00 00 02     LOCAL_SET 2          ; 存入 i
  03 00 00 00 1E     LOOP 30              ; 循环开始 (30 字节)
  20 00 00 00 02     LOCAL_GET 2          ; 加载 i
  41 00 00 00 0A     I32_CONST 10         ; 加载 10
  4B                 I32_GT_S             ; i > 10 ?
  05 00 00 00 02     BR_IF 2              ; 是→跳出
  20 00 00 00 01     LOCAL_GET 1          ; 加载 sum
  20 00 00 00 02     LOCAL_GET 2          ; 加载 i
  6A                 I32_ADD              ; sum + i
  21 00 00 00 01     LOCAL_SET 1          ; 存入 sum
  20 00 00 00 02     LOCAL_GET 2          ; 加载 i
  41 00 00 00 01     I32_CONST 1          ; 加载 1
  6A                 I32_ADD              ; i + 1
  21 00 00 00 02     LOCAL_SET 2          ; 存入 i
  04 00 00 00 03     BR 3                 ; 继续循环
```

---

## 7. SafeASM vs 标准 WASM 差异

| 特性 | 标准 WASM | SafeASM |
|------|-----------|---------|
| 扩展名 | `.wasm` | `.sasm` |
| 编码 | LEB128 变长 | **固定宽度** (4/8 字节) |
| opcode 宽度 | 1 字节 | 1 字节 |
| `memory.grow` | 允许 | ❌ 禁止 |
| `call_indirect` | 允许 | ❌ 禁止（仅直接 CALL） |
| 可变全局 | 允许 | ❌ 仅不可变 |
| 异常处理 | 提案中 | ❌ 禁止 |
| SIMD | 提案中 | ❌ 禁止 |
| 安全段 | 无 | ✅ TYPE/FUNC/MEM/IOMAP/CODE/SAFE/WCET |
| 确定性 | 部分 | ✅ 完全确定 |
| 校验和 | 无 | ✅ CRC32 校验 |
| 边界检查 | 运行时隐式 | ✅ 编译期 + 运行时显式 (SAFE_BOUNDS_CHECK) |

---

## 附录 A：`.sasm` 最小示例（十六进制）

```
; ==============================================================
; 最简单 SafeASM 程序: 返回常量 42
; 等效函数: int main() { return 42; }
; ==============================================================

; --- 文件头 ---
53 41 53 4D        ; Magic "SASM"
01                 ; Version = 1
00                 ; Flags = 0

; --- Type Section ---
00                 ; Section type = TYPE
0C 00 00 00        ; Length = 12
00 00              ; Flags = 0
00 00 00 00        ; param_count = 0
01 00 00 00        ; return_count = 1
7F 00 00 00        ; return_type = I32

; --- Function Section ---
01                 ; Section type = FUNC
0C 00 00 00        ; Length = 12
00 00              ; Flags = 0
00 00 00 00        ; type_idx = 0
00 00 00 00        ; local_count = 0

; --- Memory Section ---
02                 ; Section type = MEM
10 00 00 00        ; Length = 16
00 00              ; Flags = 0
00 01 00 00        ; total_size = 256 bytes
00 00 00 00        ; segment_count = 0

; --- IOMap Section ---
03                 ; Section type = IOMAP
04 00 00 00        ; Length = 4
00 00              ; Flags = 0
00 00 00 00        ; entry_count = 0

; --- Code Section ---
04                 ; Section type = CODE
14 00 00 00        ; Length = 20
00 00              ; Flags = 0
00 00 00 00        ; func_idx = 0
0A 00 00 00        ; body_size = 10
41 2A 00 00 00     ; I32_CONST 42
0B                 ; RETURN (indicates end)

; --- Safety Section ---
05                 ; Section type = SAFE
10 00 00 00        ; Length = 16
00 00              ; Flags = 0
01                 ; safety_level = SIL3
00 00 00 00        ; cycle_limit = 0 (unlimited)
00 00 00 00        ; stack_depth = 0
00 00 00 00        ; loop_count = 0

; --- Checksum ---
XX XX XX XX        ; CRC32 (覆盖 Magic 后所有字节)
```
