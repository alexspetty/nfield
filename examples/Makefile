CC ?= cc
PKG_CONFIG ?= pkg-config
CFLAGS ?= -O2 -std=c99 -Wall -Wextra

NFIELD_CFLAGS = $(shell $(PKG_CONFIG) --cflags nfield)
NFIELD_LIBS = $(shell $(PKG_CONFIG) --libs --static nfield)
PROGRAMS = forest_readings source_projection source_divisor

.PHONY: all run clean
all: $(PROGRAMS)

$(PROGRAMS): %: %.c
	$(PKG_CONFIG) --print-errors --exists nfield
	$(CC) $(CPPFLAGS) $(CFLAGS) $(NFIELD_CFLAGS) $< $(LDFLAGS) $(NFIELD_LIBS) $(LDLIBS) -o $@

run: all
	./forest_readings
	./source_projection
	./source_divisor

clean:
	$(RM) $(PROGRAMS)
