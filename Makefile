CHECK_FILES := $(patsubst Tests/%,check/%,$(wildcard Tests/*.m)) \
               $(patsubst examples/%,check/%,$(wildcard examples/*.m))


MAKEFLAGS += -j$(shell nproc 2> /dev/null || printf 1)

all: check

clean:
	rm Precomputations/*

check/%.m: Tests/%.m
	@magma -b filename:=$< exitsignal:='' run_tests.m
check/%.m: examples/%.m
	@magma -b filename:=$< exitsignal:='' run_tests.m

debug/%.m: Tests/%.m
	@magma -b filename:=$< debug:='' run_tests.m
debug/%.m: examples/%.m
	@magma -b filename:=$< debug:='' run_tests.m

check: $(CHECK_FILES)

print-%:
	@echo '$*=$($*)'

.PHONY: check clean
