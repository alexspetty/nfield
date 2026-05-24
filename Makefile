CC      = gcc
CFLAGS  = -O2 -Wall -Wextra -std=c99
LDFLAGS = -lm -lpthread /lib/x86_64-linux-gnu/liblapack.so.3 /lib/x86_64-linux-gnu/libblas.so.3

# Core library (no main, no verify)
LIB_SRC = src/repetend.c src/field.c src/invariants.c src/output.c src/coherence.c src/analytic.c src/scale.c
LIB_OBJ = $(LIB_SRC:.c=.o)
LIB     = libnfield.a

# Main binary
BIN     = nfield

# Verify programs
VERIFY_SRC = $(wildcard verify/*.c)
VERIFY_BIN = $(VERIFY_SRC:.c=)

all: $(BIN)

# Build static library from core sources
$(LIB): $(LIB_OBJ)
	ar rcs $@ $^

src/%.o: src/%.c src/nfield.h
	$(CC) $(CFLAGS) -c -o $@ $<

# Main binary links against library + verify + daemon
$(BIN): src/main.o src/daemon.o src/dispatch.o verify/verify.o $(LIB)
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)

src/main.o: src/main.c src/nfield.h
	$(CC) $(CFLAGS) -c -o $@ $<

src/daemon.o: src/daemon.c
	$(CC) $(CFLAGS) -c -o $@ $<

src/dispatch.o: src/dispatch.c
	$(CC) $(CFLAGS) -c -o $@ $<

verify/verify.o: verify/verify.c src/nfield.h
	$(CC) $(CFLAGS) -Isrc -c -o $@ $<

# Verify programs link against library
verify: $(VERIFY_BIN)

verify/%: verify/%.c $(LIB) src/nfield.h
	$(CC) $(CFLAGS) -Isrc -o $@ $< $(LIB) $(LDFLAGS)

# Convenience targets
parallel: CFLAGS += -fopenmp -DNFIELD_PARALLEL
parallel: all

gmp: CFLAGS += -DNFIELD_GMP
gmp: LDFLAGS += -lgmp
gmp: all

test: test-unit test-cli

test-unit: test/test_nfield.c $(LIB)
	$(CC) $(CFLAGS) -Isrc -o test/test_nfield $< $(LIB) $(LDFLAGS)
	./test/test_nfield

test-cli: $(BIN) test/test_cli_commands.sh
	bash test/test_cli_commands.sh

clean:
	rm -f $(BIN) $(LIB) src/*.o verify/*.o test/test_nfield
	find verify -maxdepth 1 -type f ! -name '*.c' ! -name '*.sh' ! -name '*.md' -delete 2>/dev/null; true

.PHONY: all parallel gmp verify test test-unit test-cli clean
