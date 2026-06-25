# Makefile — vstac 项目构建
# 编译器 (Coq) + 虚拟机 (C)

CC = gcc
CFLAGS = -Wall -Wextra -std=c11 -g -O0

# VM 测试
VM_TEST_DIR = tests/vm-tests
VM_TEST_SRCS = $(VM_TEST_DIR)/test_minimal.c
VM_TEST_BIN = $(VM_TEST_DIR)/test_minimal

# sasm_dump 工具
SASM_DUMP_SRC = vm/sasm_dump.c
SASM_DUMP_BIN = vm/sasm_dump

.PHONY: all vm-test sasm-dump clean

all: vm-test sasm-dump

# ================================================================
# VM 测试 (C)
# ================================================================

vm-test: $(VM_TEST_BIN)
	$(VM_TEST_BIN)

$(VM_TEST_BIN): $(VM_TEST_SRCS)
	$(CC) $(CFLAGS) -o $@ $<

# ================================================================
# sasm_dump 工具
# ================================================================

sasm-dump: $(SASM_DUMP_BIN)

$(SASM_DUMP_BIN): $(SASM_DUMP_SRC)
	$(CC) $(CFLAGS) -o $@ $<

# ================================================================
# Coq 编译器 (需要 dune + coq)
# ================================================================

# 在 Phase 1 实现后启用:
# coq-build:
# 	cd vstac && dune build

# ================================================================
# 清理
# ================================================================

clean:
	rm -f $(VM_TEST_BIN)
	find . -name '*.o' -delete
