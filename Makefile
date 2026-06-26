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

.PHONY: all coq vm-test sasm-dump clean

all: coq vm-test sasm-dump

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
# Coq/Rocq 编译器
# ================================================================

VSTAC_DIR = vstac
ROQC = coqc
ROQCFLAGS = -Q spec vstac_spec -Q src vstac_src

# Spec files (compile in order due to dependencies)
SPEC_FILES = spec/safeasm.v spec/safest.v spec/compiler_correctness.v

# Src files (depend on spec files)
SRC_FILES = src/encoder.v src/lexer.v src/parser.v src/desugar.v src/typechecker.v src/codegen.v

coq:
	@echo "  [ROQC] spec files..."
	cd $(VSTAC_DIR) && for f in $(SPEC_FILES); do \
		echo "    $$f"; $(ROQC) $(ROQCFLAGS) $$f || exit 1; \
	done
	@echo "  [ROQC] src files..."
	cd $(VSTAC_DIR) && for f in $(SRC_FILES); do \
		echo "    $$f"; $(ROQC) $(ROQCFLAGS) $$f || exit 1; \
	done
	@echo "  [ROQC] All files compiled successfully"

# ================================================================
# 清理
# ================================================================

clean:
	rm -f $(VM_TEST_BIN)
	find . -name '*.o' -delete

	rm -f vstac/spec/*.vo vstac/spec/*.glob vstac/src/*.vo vstac/src/*.glob vstac/*.vo vstac/*.glob
	cd vstac && dune clean 2>/dev/null || true