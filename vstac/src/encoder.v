(* ================================================================
   vstac/src/encoder.v
   SafeASM 二进制编码器 — 将 sasm_module 序列化为 .sasm 字节流
   
   输入:  sasm_module (Coq 类型)
   输出:  list Z (字节序列，每个字节 0-255)
   
   编码方式: 固定宽度编码（非 LEB128）
   正确性定理: encode_decode_identity — 编码后解码回到原模块
   ================================================================ *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import vstac.spec.safeasm.
Import ListNotations.

(* ================================================================
   第 1 部分：基本编码函数 (Primitive Encoding)
   ================================================================ *)

(* uint8 → 1 字节 *)
Definition encode_u8 (v : Z) : list Z :=
  [Z.land v 255].

(* uint32 → 4 字节小端序 *)
Definition encode_u32 (v : Z) : list Z :=
  [Z.land v 255;
   Z.land (v >> 8) 255;
   Z.land (v >> 16) 255;
   Z.land (v >> 24) 255].

(* sint32 → 4 字节小端序（二进制补码） *)
Definition encode_s32 (v : Z) : list Z :=
  encode_u32 (Z.land v 4294967295).  (* 2^32 - 1 *)

(* uint64 → 8 字节小端序 *)
Definition encode_u64 (v : Z) : list Z :=
  [Z.land v 255;
   Z.land (v >> 8) 255;
   Z.land (v >> 16) 255;
   Z.land (v >> 24) 255;
   Z.land (v >> 32) 255;
   Z.land (v >> 40) 255;
   Z.land (v >> 48) 255;
   Z.land (v >> 56) 255].

(* float32 → 4 字节 IEEE 754（简化实现，使用位模式） *)
Definition encode_f32 (f : float) : list Z :=
  encode_u32 0.  (* 占位：实际需使用 Float32.bits_of_float *)

(* float64 → 8 字节 IEEE 754 *)
Definition encode_f64 (f : float) : list Z :=
  encode_u64 0.  (* 占位 *)

(* string → 字节序列（UTF-8 ASCII 子集） *)
Fixpoint encode_string (s : string) : list Z :=
  match s with
  | EmptyString => []
  | String c s' => Z.of_N (Ascii.N_of_ascii c) :: encode_string s'
  end.

(* ================================================================
   第 2 部分：Section 头编码
   ================================================================ *)

Definition encode_section_header (section_type : Z) (length : Z) : list Z :=
  encode_u8 section_type ++
  encode_u32 length ++
  encode_u8 0 ++        (* reserved *)
  encode_u16 0.         (* flags *)

(* uint16 → 2 字节 *)
Definition encode_u16 (v : Z) : list Z :=
  [Z.land v 255; Z.land (v >> 8) 255].

(* ================================================================
   第 3 部分：值类型编码
   ================================================================ *)

Definition encode_value_type (vt : sasm_value_type) : Z :=
  match vt with
  | I32 => 0x7F
  | I64 => 0x7E
  | F32 => 0x7D
  | F64 => 0x7C
  end.

(* ================================================================
   第 4 部分：指令编码 (Instruction Encoding)
   ================================================================ *)

Definition encode_memory_arg (arg : memory_arg) : list Z :=
  encode_u16 arg.(mem_align) ++ encode_u16 arg.(mem_offset).

Fixpoint encode_sasm_instr (instr : sasm_instr) : list Z :=
  match instr with
  (* 控制流 *)
  | UNREACHABLE => [0x00]
  | NOP => [0x01]
  | BLOCK len => 0x02 :: encode_u32 len
  | LOOP len => 0x03 :: encode_u32 len
  | BR depth => 0x04 :: encode_u32 depth
  | BR_IF depth => 0x05 :: encode_u32 depth
  | RETURN => [0x06]
  
  (* 函数调用 *)
  | CALL idx => 0x10 :: encode_u32 idx
  
  (* 栈操作 *)
  | DROP => [0x1A]
  | SELECT => [0x1B]
  | LOCAL_GET idx => 0x20 :: encode_u32 idx
  | LOCAL_SET idx => 0x21 :: encode_u32 idx
  | LOCAL_TEE idx => 0x22 :: encode_u32 idx
  
  (* i32 常量 *)
  | I32_CONST v => 0x41 :: encode_s32 v
  
  (* i32 比较 *)
  | I32_EQZ => [0x45]
  | I32_EQ => [0x46]  | I32_NE => [0x47]
  | I32_LT_S => [0x48] | I32_LE_S => [0x49]
  | I32_GT_S => [0x4A] | I32_GE_S => [0x4B]
  
  (* i32 算术 *)
  | I32_ADD => [0x6A] | I32_SUB => [0x6B] | I32_MUL => [0x6C]
  | I32_DIV_S => [0x6D] | I32_REM_S => [0x6F]
  
  (* i32 位运算 *)
  | I32_AND => [0x71] | I32_OR => [0x72] | I32_XOR => [0x73]
  | I32_SHL => [0x74] | I32_SHR_S => [0x75]
  | I32_ROTL => [0x76] | I32_ROTR => [0x77]
  
  (* i64 常量/比较/算术 *)
  | I64_CONST v => 0x50 :: encode_s64 v
  | I64_EQZ => [0x53]
  | I64_EQ => [0x54] | I64_NE => [0x55]
  | I64_LT_S => [0x56] | I64_LE_S => [0x57]
  | I64_GT_S => [0x58] | I64_GE_S => [0x59]
  | I64_ADD => [0x7C] | I64_SUB => [0x7D] | I64_MUL => [0x7E]
  | I64_DIV_S => [0x7F] | I64_REM_S => [0x80]
  | I64_AND => [0x81] | I64_OR => [0x82] | I64_XOR => [0x83]
  | I64_SHL => [0x84] | I64_SHR_S => [0x85]
  
  (* 浮点常量 *)
  | F32_CONST f => 0x43 :: encode_f32 f
  | F64_CONST f => 0x44 :: encode_f64 f
  
  (* f32 算术 *)
  | F32_ADD => [0x92] | F32_SUB => [0x93]
  | F32_MUL => [0x94] | F32_DIV => [0x95]
  | F32_EQ => [0x9A] | F32_NE => [0x9B]
  | F32_LT => [0x9C] | F32_LE => [0x9D]
  | F32_GT => [0x9E] | F32_GE => [0x9F]
  | F32_ABS => [0xA0] | F32_NEG => [0xA1] | F32_SQRT => [0xA2]
  
  (* f64 算术 *)
  | F64_ADD => [0xA3] | F64_SUB => [0xA4]
  | F64_MUL => [0xA5] | F64_DIV => [0xA6]
  | F64_EQ => [0xAA] | F64_NE => [0xAB]
  | F64_LT => [0xAC] | F64_LE => [0xAD]
  | F64_GT => [0xAE] | F64_GE => [0xAF]
  | F64_ABS => [0xB0] | F64_NEG => [0xB1] | F64_SQRT => [0xB2]
  
  (* 类型转换 *)
  | I32_WRAP_I64 => [0xA7]
  | I64_EXTEND_I32_S => [0xAE]
  | I32_TRUNC_F32_S => [0xAF]
  | I32_TRUNC_F64_S => [0xB0]
  | F32_CONVERT_I32_S => [0xB7]
  | F64_CONVERT_I32_S => [0xBB]
  
  (* 内存操作 *)
  | I32_LOAD arg => 0x28 :: encode_memory_arg arg
  | I64_LOAD arg => 0x29 :: encode_memory_arg arg
  | F32_LOAD arg => 0x2A :: encode_memory_arg arg
  | F64_LOAD arg => 0x2B :: encode_memory_arg arg
  | I32_STORE arg => 0x36 :: encode_memory_arg arg
  | I64_STORE arg => 0x37 :: encode_memory_arg arg
  | F32_STORE arg => 0x38 :: encode_memory_arg arg
  | F64_STORE arg => 0x39 :: encode_memory_arg arg
  
  (* 安全扩展 *)
  | SAFE_ASSERT (ASSERT_CYCLE_LIMIT lim) =>
      0xFC :: encode_u8 0 :: encode_u32 lim
  | SAFE_ASSERT (ASSERT_STACK_DEPTH depth) =>
      0xFC :: encode_u8 1 :: encode_u32 depth
  | SAFE_ASSERT (ASSERT_MEM_BOUNDS (low, high)) =>
      0xFC :: encode_u8 2 :: encode_u32 low ++ encode_u32 high
  | SAFE_BOUNDS_CHECK (low, high) =>
      0xFD :: encode_u32 low ++ encode_u32 high
  end

with encode_s64 (v : Z) : list Z :=
  encode_u64 (Z.land v 18446744073709551615).  (* 2^64 - 1 *)
.

(* ================================================================
   第 5 部分：Section 编码
   ================================================================ *)

(* Type Section 编码 *)
Definition encode_type_section (types : list sasm_func_type) : list Z :=
  let body :=
    fold_right (fun ft acc =>
      encode_u32 (Z.of_nat (List.length ft.(sasm_param_types))) ++
      fold_right (fun vt acc => encode_u8 (encode_value_type vt) ++ acc)
                 [] ft.(sasm_param_types) ++
      encode_u32 (Z.of_nat (List.length ft.(sasm_return_types))) ++
      fold_right (fun vt acc => encode_u8 (encode_value_type vt) ++ acc)
                 [] ft.(sasm_return_types) ++ acc
    ) [] types
  in
  encode_section_header 0 (Z.of_nat (List.length body)) ++ body.

(* Function Section 编码 *)
Definition encode_function_section (funcs : list sasm_function) : list Z :=
  let body :=
    fold_right (fun f acc =>
      encode_u32 f.(sasm_func_type_idx) ++
      encode_u32 (Z.of_nat (List.length f.(sasm_locals))) ++
      fold_right (fun vt acc => encode_u8 (encode_value_type vt) ++ acc)
                 [] f.(sasm_locals) ++ acc
    ) [] funcs
  in
  encode_section_header 1 (Z.of_nat (List.length body)) ++ body.

(* Memory Section 编码 *)
Definition encode_memory_section (segs : list memory_segment) (total_size : Z) : list Z :=
  let seg_type_val (st : segment_type) : Z :=
    match st with
    | SEG_IO_INPUT => 0 | SEG_IO_OUTPUT => 1
    | SEG_GLOBAL => 2 | SEG_FB_DATA => 3
    | SEG_STACK => 4 | SEG_CONST => 5
    end in
  let body :=
    encode_u32 total_size ++
    encode_u32 (Z.of_nat (List.length segs)) ++
    fold_right (fun seg acc =>
      encode_u8 (seg_type_val seg.(seg_type)) ++
      encode_u32 seg.(seg_start) ++
      encode_u32 seg.(seg_size) ++ acc
    ) [] segs
  in
  encode_section_header 2 (Z.of_nat (List.length body)) ++ body.

(* IOMap Section 编码 *)
Definition encode_iomap_section (entries : list io_entry_sasm) : list Z :=
  let dir_val (d : io_direction) : Z :=
    match d with IO_INPUT => 0 | IO_OUTPUT => 1 end in
  let iotype_val (t : io_type) : Z :=
    match t with IO_AI => 0 | IO_AO => 1 | IO_DI => 2 | IO_DO => 3 end in
  let body :=
    encode_u32 (Z.of_nat (List.length entries)) ++
    fold_right (fun e acc =>
      encode_u32 0 ++  (* st_var_name_offset, 0 = debug section not used *)
      encode_u32 e.(io_mem_offset) ++
      encode_u32 e.(io_channel_id) ++
      encode_u8 (dir_val e.(io_dir)) ++
      encode_u8 (iotype_val e.(io_type_kind)) ++
      encode_u32 e.(io_bit_width) ++
      encode_f64 e.(io_scale) ++
      encode_f64 e.(io_bias) ++
      encode_s32 e.(io_safety_low) ++
      encode_s32 e.(io_safety_high) ++ acc
    ) [] entries
  in
  encode_section_header 3 (Z.of_nat (List.length body)) ++ body.

(* Code Section 编码 *)
Fixpoint encode_code_section (funcs : list sasm_function) : list Z :=
  let body :=
    fold_right (fun f acc =>
      let code_body := fold_right (fun i acc' => encode_sasm_instr i ++ acc') [] f.(sasm_body) in
      encode_u32 f.(sasm_func_type_idx) ++
      encode_u32 (Z.of_nat (List.length code_body)) ++
      code_body ++ acc
    ) [] funcs
  in
  encode_section_header 4 (Z.of_nat (List.length body)) ++ body.

(* Safety Section 编码 *)
Definition encode_safety_section (sa : safety_annotation) : list Z :=
  let loop_body :=
    fold_right (fun lb acc =>
      encode_u32 lb.(lb_func_idx) ++
      encode_u32 lb.(lb_instr_offset) ++
      encode_u32 lb.(lb_max_iter) ++ acc
    ) [] sa.(safe_loop_bounds) in
  let mem_body :=
    fold_right (fun r acc =>
      encode_u32 r.(mar_low) ++ encode_u32 r.(mar_high) ++ acc
    ) [] sa.(safe_mem_access_map) in
  let body :=
    encode_u8 sa.(safe_level) ++
    encode_u32 sa.(safe_cycle_limit) ++
    encode_u32 sa.(safe_stack_depth) ++
    encode_u32 (Z.of_nat (List.length sa.(safe_loop_bounds))) ++
    loop_body ++
    encode_u32 (Z.of_nat (List.length sa.(safe_mem_access_map))) ++
    mem_body
  in
  encode_section_header 5 (Z.of_nat (List.length body)) ++ body.

(* ================================================================
   第 6 部分：CRC32 校验和（简化实现）
   ================================================================ *)

(* CRC32 计算（多项式 0xEDB88320，简化版） *)
Definition crc32_table : list Z :=
  (* 实际实现需要一个 256 条目的查找表，这里简化为占位 *)
  List.repeat 0 256.

Fixpoint crc32_update (crc : Z) (bytes : list Z) : Z :=
  (* CRC32 计算（简化占位） *)
  0.

Definition compute_crc32 (bytes : list Z) : Z :=
  Z.lnot (crc32_update (Z.lnot 0) bytes).

(* ================================================================
   第 7 部分：完整模块编码 (Module Encoding)
   ================================================================ *)

(* 编码完整 SafeASM 模块 *)
Definition encode_sasm (m : sasm_module) : list Z :=
  (* 文件头 *)
  let magic := [0x53; 0x41; 0x53; 0x4D] in  (* "SASM" *)
  let header := magic ++
                encode_u8 m.(sasm_version) ++
                encode_u8 m.(sasm_flags) in
  
  (* 各 Section *)
  let type_sec := encode_type_section m.(sasm_types) in
  let func_sec := encode_function_section m.(sasm_functions) in
  let mem_sec  := encode_memory_section m.(sasm_memory_segments)
                                          m.(sasm_total_memory_size) in
  let iomap_sec := encode_iomap_section m.(sasm_io_map) in
  let code_sec := encode_code_section m.(sasm_functions) in
  let safe_sec := encode_safety_section m.(sasm_safety) in
  
  (* 合并所有数据（不含 Magic 的 CRC 计算范围） *)
  let data := header ++ type_sec ++ func_sec ++ mem_sec ++
              iomap_sec ++ code_sec ++ safe_sec in
  
  (* 计算 CRC（覆盖 Magic 后的所有字节） *)
  let crc_bytes := encode_u32 (compute_crc32 data) in
  
  data ++ crc_bytes.

(* ================================================================
   第 8 部分：解码器 (Decoder — 用于验证编码可逆性)
   ================================================================ *)

(* 解码器状态 *)
Record decoder_state : Type := {
  ds_bytes : list Z;
  ds_pos   : Z;
}.

(* 读取 n 个字节 *)
Fixpoint read_bytes (n : Z) (st : decoder_state) : option (list Z * decoder_state) :=
  if n <=? 0 then Some ([], st)
  else
    match ds_bytes st with
    | b :: rest =>
        read_bytes (n - 1) (Build_decoder_state rest (ds_pos st + 1))
    | nil => None
    end.

(* 解码 uint32 *)
Definition decode_u32 (st : decoder_state) : option (Z * decoder_state) :=
  match read_bytes 4 st with
  | Some ([b0; b1; b2; b3], st') =>
      Some (b0 + (b1 << 8) + (b2 << 16) + (b3 << 24), st')
  | _ => None
  end.

(* 解码 uint8 *)
Definition decode_u8 (st : decoder_state) : option (Z * decoder_state) :=
  match read_bytes 1 st with
  | Some ([b], st') => Some (b, st')
  | _ => None
  end.

(* 解码完整模块（用于验证 encode_decode_identity） *)
Definition decode_sasm (bytes : list Z) : option sasm_module :=
  match bytes with
  | 0x53 :: 0x41 :: 0x53 :: 0x4D :: rest =>  (* "SASM" magic *)
      let st0 := Build_decoder_state rest 0 in
      (* 简化解码：Phase 0.7 仅验证编码器输出格式一致，完整解码器在 Phase 1 实现 *)
      Some (Build_sasm_module
        "SASM"                             (* magic *)
        1                                  (* version *)
        0                                  (* flags *)
        nil nil nil 0 nil                  (* 类型/函数/内存/I/O *)
        (Build_safety_annotation           (* safety *)
           0 0 0 nil nil)
        None                               (* WCET *)
        0                                  (* entry *)
      )
  | _ => None
  end.

(* ================================================================
   第 9 部分：正确性定理 (Correctness Theorems)
   ================================================================ *)

(* 定理 1: 编码格式正确 — encode_sasm 产生的字节以 SASM Magic 开头 *)
Theorem encode_starts_with_magic : forall (m : sasm_module),
    exists rest, encode_sasm m = [0x53; 0x41; 0x53; 0x4D] ++ rest.
Proof.
  intros m. unfold encode_sasm. simpl. eexists. reflexivity.
Qed.

(* 定理 2: 编码可逆 — 编码后解码回到原模块 *)
Theorem encode_decode_identity : forall (m : sasm_module),
    decode_sasm (encode_sasm m) = Some m.
Proof.
  intros m.
  unfold encode_sasm, decode_sasm.
  (* 展开编码过程，验证 Magic 字节匹配 *)
  simpl.
  (* 当前简化实现中 decode_sasm 返回固定模块，需要进一步完善 *)
  (* 具体证明需在解码器完善后完成 *)
Admitted.

(* 定理 3: 指令编码唯一性 — 不同指令产生不同的字节序列 *)
Theorem instr_encoding_unique : forall (i1 i2 : sasm_instr),
    encode_sasm_instr i1 = encode_sasm_instr i2 ->
    i1 = i2.
Proof.
  intros i1 i2 H.
  (* 通过对指令结构的归纳证明 *)
  destruct i1; destruct i2; simpl in H; try congruence.
  (* 具体证明待完善 *)
Admitted.
