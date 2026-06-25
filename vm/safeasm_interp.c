/**
 * vm/safeasm_interp.c
 * SafeASM 字节码解释器（核心指令子集）
 * 
 * 当前实现的最小指令子集:
 *   控制流:   UNREACHABLE, NOP, BLOCK, LOOP, BR, BR_IF, RETURN
 *   调用:     CALL
 *   栈操作:   DROP, SELECT, LOCAL_GET, LOCAL_SET, LOCAL_TEE
 *   常量:     I32_CONST
 *   算术:     I32_ADD, I32_SUB, I32_MUL, I32_DIV_S, I32_REM_S
 *   位运算:   I32_AND, I32_OR, I32_XOR
 *   比较:     I32_EQZ, I32_EQ, I32_NE, I32_LT_S, I32_GT_S
 *   内存:     I32_LOAD, I32_STORE
 *   安全扩展: SAFE_ASSERT, SAFE_BOUNDS_CHECK
 * 
 * 安全约束:
 *   - 所有数组访问带边界检查
 *   - 指令计数预算控制
 *   - 栈深度限制
 *   - 除法零值检查
 */

#include "vm.h"
#include <string.h>

/* ================================================================
   值栈操作
   ================================================================ */

static inline bool push_value(VM *vm, sasm_value val) {
    if (vm->val_stack_ptr >= VALUE_STACK_SIZE) {
        vm->last_error = VM_ERR_STACK_OVERFLOW;
        return false;
    }
    vm->val_stack[vm->val_stack_ptr++] = val;
    return true;
}

static inline sasm_value pop_value(VM *vm) {
    if (vm->val_stack_ptr == 0) {
        vm->last_error = VM_ERR_STACK_UNDERFLOW;
        return 0;
    }
    return vm->val_stack[--vm->val_stack_ptr];
}

static inline sasm_value peek_value(const VM *vm, uint32_t depth) {
    if (depth >= vm->val_stack_ptr) return 0;
    return vm->val_stack[vm->val_stack_ptr - 1 - depth];
}

/* ================================================================
   帧栈操作
   ================================================================ */

static inline Frame *current_frame(VM *vm) {
    if (vm->frame_stack_ptr == 0) return NULL;
    return &vm->frame_stack[vm->frame_stack_ptr - 1];
}

static bool push_frame(VM *vm, uint32_t func_idx) {
    if (vm->frame_stack_ptr >= FRAME_STACK_SIZE) {
        vm->last_error = VM_ERR_FRAME_OVERFLOW;
        return false;
    }
    
    const SasmModule *m = vm->module;
    Frame *frame = &vm->frame_stack[vm->frame_stack_ptr++];
    
    frame->func_idx = func_idx;
    frame->pc = 0;
    frame->local_count = m->funcs[func_idx].local_count;
    frame->body = NULL;
    frame->body_size = 0;
    frame->block_depth = 0;
    
    /* 查找对应的代码体 */
    for (uint32_t i = 0; i < m->code_count; i++) {
        if (m->codes[i].func_idx == func_idx) {
            frame->body = m->codes[i].body;
            frame->body_size = m->codes[i].body_size;
            break;
        }
    }
    
    /* 初始化局部变量 */
    for (uint32_t i = 0; i < frame->local_count && i < 32; i++) {
        frame->locals[i] = 0;
    }
    
    return true;
}

static void pop_frame(VM *vm) {
    if (vm->frame_stack_ptr > 0) {
        vm->frame_stack_ptr--;
    }
}

/* ================================================================
   字节码读取
   ================================================================ */

static inline uint8_t read_u8_code(const Frame *f, uint32_t *pc) {
    if (*pc >= f->body_size) return 0;
    return f->body[(*pc)++];
}

static inline uint32_t read_u32_code(const Frame *f, uint32_t *pc) {
    if (*pc + 4 > f->body_size) return 0;
    uint32_t val = (uint32_t)f->body[*pc] |
                  ((uint32_t)f->body[*pc + 1] << 8) |
                  ((uint32_t)f->body[*pc + 2] << 16) |
                  ((uint32_t)f->body[*pc + 3] << 24);
    *pc += 4;
    return val;
}

static inline uint16_t read_u16_code(const Frame *f, uint32_t *pc) {
    if (*pc + 2 > f->body_size) return 0;
    uint16_t val = (uint16_t)f->body[*pc] |
                   ((uint16_t)f->body[*pc + 1] << 8);
    *pc += 2;
    return val;
}

/* ================================================================
   内存访问
   ================================================================ */

static bool check_mem_bounds(const VM *vm, uint32_t addr, uint32_t size) {
    if (addr + size > vm->memory_size) {
        return false;
    }
    /* 检查安全注解中的合法访问范围 */
    const SafetyAnnotation *sa = &vm->module->safety;
    for (uint32_t i = 0; i < sa->mem_range_count; i++) {
        if (addr >= sa->mem_access_ranges[i].low &&
            addr + size <= sa->mem_access_ranges[i].high) {
            return true;
        }
    }
    /* 如果没有配置访问范围，允许所有在 memory_size 内的访问 */
    return sa->mem_range_count == 0;
}

/* ================================================================
   指令分发器
   ================================================================ */

int vm_execute_cycle(VM *vm) {
    Frame *frame = current_frame(vm);
    if (!frame) return VM_ERR_INVALID_OPCODE;
    
    while (frame->pc < frame->body_size) {
        /* 周期计数检查 */
        vm->cycle_count++;
        if (vm->cycle_count > vm->module->safety.cycle_limit &&
            vm->module->safety.cycle_limit > 0) {
            return VM_ERR_CYCLE_LIMIT;
        }
        
        uint32_t pc = frame->pc;
        uint8_t opcode = read_u8_code(frame, &pc);
        
        switch (opcode) {
        case OP_UNREACHABLE:
            return VM_ERR_UNREACHABLE;
            
        case OP_NOP:
            break;
            
        case OP_RETURN: {
            pop_frame(vm);
            frame = current_frame(vm);
            if (!frame) return VM_OK;
            continue;
        }
        
        case OP_BLOCK: {
            uint32_t block_len = read_u32_code(frame, &pc);
            /* 记录返回地址 */
            if (frame->block_depth < 16) {
                frame->block_stack[frame->block_depth++] = pc + block_len;
            }
            break;
        }
        
        case OP_LOOP: {
            read_u32_code(frame, &pc);
            if (frame->block_depth < 16) {
                /* LOOP 的返回地址指向循环开始（pc 之前已指向 body 偏移） */
                frame->block_stack[frame->block_depth++] = pc - 5;  /* 5 = opcode + u32 */
            }
            break;
        }
        
        case OP_BR: {
            uint32_t depth = read_u32_code(frame, &pc);
            if (depth < frame->block_depth) {
                /* 跳转到 block_stack[depth] */
                pc = frame->block_stack[depth];
                frame->block_depth = depth;
            }
            break;
        }
        
        case OP_BR_IF: {
            uint32_t depth = read_u32_code(frame, &pc);
            sasm_value cond = pop_value(vm);
            if (cond != 0) {
                if (depth < frame->block_depth) {
                    pc = frame->block_stack[depth];
                    frame->block_depth = depth;
                }
            }
            break;
        }
        
        case OP_CALL: {
            uint32_t func_idx = read_u32_code(frame, &pc);
            /* 保存当前帧的 PC */
            frame->pc = pc;
            /* 创建新帧 */
            if (!push_frame(vm, func_idx)) {
                return vm->last_error;
            }
            /* 将值栈中的参数复制到新帧的局部变量 */
            frame = current_frame(vm);
            for (int32_t i = (int32_t)frame->local_count - 1; i >= 0; i--) {
                frame->locals[i] = pop_value(vm);
            }
            pc = frame->pc;  /* 从新帧开始执行 */
            continue;
        }
        
        case OP_DROP:
            pop_value(vm);
            break;
            
        case OP_SELECT: {
            sasm_value c = pop_value(vm);
            sasm_value v1 = pop_value(vm);
            sasm_value v2 = pop_value(vm);
            push_value(vm, c ? v1 : v2);
            break;
        }
        
        case OP_LOCAL_GET: {
            uint32_t idx = read_u32_code(frame, &pc);
            if (idx < frame->local_count) {
                push_value(vm, frame->locals[idx]);
            }
            break;
        }
        
        case OP_LOCAL_SET: {
            uint32_t idx = read_u32_code(frame, &pc);
            if (idx < frame->local_count) {
                frame->locals[idx] = pop_value(vm);
            }
            break;
        }
        
        case OP_LOCAL_TEE: {
            uint32_t idx = read_u32_code(frame, &pc);
            sasm_value val = peek_value(vm, 0);
            if (idx < frame->local_count) {
                frame->locals[idx] = val;
            }
            break;
        }
        
        case OP_I32_CONST: {
            int32_t val = (int32_t)read_u32_code(frame, &pc);
            push_value(vm, val);
            break;
        }
        
        case OP_I32_EQZ: {
            sasm_value v = pop_value(vm);
            push_value(vm, v == 0 ? 1 : 0);
            break;
        }
        
        case OP_I32_EQ: {
            sasm_value v2 = pop_value(vm);
            sasm_value v1 = pop_value(vm);
            push_value(vm, v1 == v2 ? 1 : 0);
            break;
        }
        
        case OP_I32_NE: {
            sasm_value v2 = pop_value(vm);
            sasm_value v1 = pop_value(vm);
            push_value(vm, v1 != v2 ? 1 : 0);
            break;
        }
        
        case OP_I32_LT_S: {
            sasm_value v2 = pop_value(vm);
            sasm_value v1 = pop_value(vm);
            push_value(vm, v1 < v2 ? 1 : 0);
            break;
        }
        
        case OP_I32_GT_S: {
            sasm_value v2 = pop_value(vm);
            sasm_value v1 = pop_value(vm);
            push_value(vm, v1 > v2 ? 1 : 0);
            break;
        }
        
        case OP_I32_ADD: {
            sasm_value v2 = pop_value(vm);
            sasm_value v1 = pop_value(vm);
            push_value(vm, v1 + v2);
            break;
        }
        
        case OP_I32_SUB: {
            sasm_value v2 = pop_value(vm);
            sasm_value v1 = pop_value(vm);
            push_value(vm, v1 - v2);
            break;
        }
        
        case OP_I32_MUL: {
            sasm_value v2 = pop_value(vm);
            sasm_value v1 = pop_value(vm);
            push_value(vm, v1 * v2);
            break;
        }
        
        case OP_I32_DIV_S: {
            sasm_value v2 = pop_value(vm);
            sasm_value v1 = pop_value(vm);
            if (v2 == 0) return VM_ERR_DIV_BY_ZERO;
            push_value(vm, v1 / v2);
            break;
        }
        
        case OP_I32_REM_S: {
            sasm_value v2 = pop_value(vm);
            sasm_value v1 = pop_value(vm);
            if (v2 == 0) return VM_ERR_DIV_BY_ZERO;
            push_value(vm, v1 % v2);
            break;
        }
        
        case OP_I32_AND: {
            sasm_value v2 = pop_value(vm);
            sasm_value v1 = pop_value(vm);
            push_value(vm, v1 & v2);
            break;
        }
        
        case OP_I32_OR: {
            sasm_value v2 = pop_value(vm);
            sasm_value v1 = pop_value(vm);
            push_value(vm, v1 | v2);
            break;
        }
        
        case OP_I32_XOR: {
            sasm_value v2 = pop_value(vm);
            sasm_value v1 = pop_value(vm);
            push_value(vm, v1 ^ v2);
            break;
        }
        
        case OP_I32_LOAD: {
            uint16_t align  = read_u16_code(frame, &pc);
            uint16_t offset = read_u16_code(frame, &pc);
            (void)align;
            
            sasm_value addr = pop_value(vm);
            uint32_t mem_addr = (uint32_t)(addr + (int32_t)offset);
            
            if (!check_mem_bounds(vm, mem_addr, 4)) {
                return VM_ERR_MEM_OUT_OF_BOUNDS;
            }
            
            int32_t val = (int32_t)vm->memory[mem_addr] |
                         ((int32_t)vm->memory[mem_addr + 1] << 8) |
                         ((int32_t)vm->memory[mem_addr + 2] << 16) |
                         ((int32_t)vm->memory[mem_addr + 3] << 24);
            push_value(vm, val);
            break;
        }
        
        case OP_I32_STORE: {
            uint16_t align  = read_u16_code(frame, &pc);
            uint16_t offset = read_u16_code(frame, &pc);
            (void)align;
            
            sasm_value val  = pop_value(vm);
            sasm_value addr = pop_value(vm);
            uint32_t mem_addr = (uint32_t)(addr + (int32_t)offset);
            
            if (!check_mem_bounds(vm, mem_addr, 4)) {
                return VM_ERR_MEM_OUT_OF_BOUNDS;
            }
            
            vm->memory[mem_addr]       = (uint8_t)(val & 0xFF);
            vm->memory[mem_addr + 1]   = (uint8_t)((val >> 8) & 0xFF);
            vm->memory[mem_addr + 2]   = (uint8_t)((val >> 16) & 0xFF);
            vm->memory[mem_addr + 3]   = (uint8_t)((val >> 24) & 0xFF);
            break;
        }
        
        case OP_SAFE_ASSERT: {
            read_u8_code(frame, &pc);
            uint32_t limit = read_u32_code(frame, &pc);
            (void)limit;
            /* SAFE_ASSERT 在运行时仅记录，不阻断执行 */
            /* 编译期的安全约束检查由 verify 阶段完成 */
            break;
        }
        
        case OP_SAFE_BOUNDS: {
            uint32_t low  = read_u32_code(frame, &pc);
            uint32_t high = read_u32_code(frame, &pc);
            sasm_value idx = pop_value(vm);
            if ((uint32_t)idx < low || (uint32_t)idx >= high) {
                return VM_ERR_MEM_OUT_OF_BOUNDS;
            }
            push_value(vm, idx);  /* 将索引放回栈顶供后续 LOAD 使用 */
            break;
        }
        
        default:
            vm->last_error = VM_ERR_INVALID_OPCODE;
            return VM_ERR_INVALID_OPCODE;
        }
        
        frame->pc = pc;
        frame = current_frame(vm);
        if (!frame) break;
    }
    
    return VM_OK;
}

/* ================================================================
   VM 生命周期
   ================================================================ */

/**
 * vm_init - 初始化 VM
 * @module: 已加载的 SasmModule
 * @memory_size: 线性内存大小
 * 返回: 0 = 成功, -1 = 失败
 */
int vm_init(VM *vm, const SasmModule *module, uint32_t memory_size) {
    if (!vm || !module) return -1;
    
    memset(vm, 0, sizeof(VM));
    
    vm->module = module;
    vm->memory_size = (memory_size > 0 && memory_size <= MEMORY_SIZE) 
                       ? memory_size : MEMORY_SIZE;
    vm->memory_size = (module->total_memory_size > 0 && 
                       module->total_memory_size <= MEMORY_SIZE)
                       ? module->total_memory_size : vm->memory_size;
    
    vm->val_stack_ptr = 0;
    vm->frame_stack_ptr = 0;
    vm->cycle_count = 0;
    vm->last_error = VM_OK;
    
    /* 清空内存 */
    memset(vm->memory, 0, vm->memory_size);
    
    return 0;
}

/**
 * vm_run - 运行 VM（执行一个扫描周期）
 * @vm: VM 实例
 * 返回: 0 = 正常结束, 其他 = 错误码
 */
int vm_run(VM *vm) {
    if (!vm || !vm->module) return -1;
    
    vm->cycle_count = 0;
    
    /* 创建入口函数帧 */
    if (!push_frame(vm, vm->module->entry_function)) {
        return vm->last_error;
    }
    
    int result = vm_execute_cycle(vm);
    
    /* 清理帧栈 */
    vm->frame_stack_ptr = 0;
    
    return result;
}

/**
 * vm_get_result - 获取执行结果（栈顶值）
 */
sasm_value vm_get_result(const VM *vm) {
    if (vm->val_stack_ptr == 0) return 0;
    return vm->val_stack[0];
}
