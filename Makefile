CHECK_FILES := $(patsubst Tests/%,check/%,$(wildcard Tests/*.m)) \
               $(patsubst examples/%,check/%,$(wildcard examples/*.m))
SLOW_CHECK_FILES := $(patsubst Tests/%,check/%,$(wildcard Tests/slow/*.m)) \
                    $(patsubst examples/%,check/%,$(wildcard examples/slow/*.m))


MAKEFLAGS += -j$(shell nproc 2> /dev/null || printf 1)

all: check

clean:
	rm Precomputations/*

check/%.m: Tests/%.m | check-no-dups
	@magma -b filename:=$< exitsignal:='' run_tests.m
check/%.m: examples/%.m | check-no-dups
	@magma -b filename:=$< exitsignal:='' run_tests.m

debug/%.m: Tests/%.m | check-no-dups
	@magma -b filename:=$< debug:='' run_tests.m
debug/%.m: examples/%.m | check-no-dups
	@magma -b filename:=$< debug:='' run_tests.m

check: $(CHECK_FILES)

check-slow: $(SLOW_CHECK_FILES)

check-no-dups:
	@sh scripts/no_dup_test_basenames.sh

print-%:
	@echo '$*=$($*)'

.PHONY: check check-slow clean check-no-dups
