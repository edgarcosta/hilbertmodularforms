// test-time: ~2m
// HilbertModularVariety end-to-end test: Q(sqrt(5)), level 3*ZF
// 3 is inert in Q(sqrt(5)), so 3*ZF is a prime ideal of norm 9
// Known: generators in weights [2,2,4,6,8], relations in weights [8,16]
// Expected: 1 component, certified, dimension 2
// Resources: ~2.5 min CPU, ~305 MB RAM
printf "HilbertModularVariety on Q(sqrt(5)), level 3*ZF...";
t0 := Cputime(); walltime := Time();
F := QuadraticField(5);
ZF := Integers(F);
NN := 3*ZF;
comp_data, schemes, certified := HilbertModularVariety(F, NN : MaxB := 20);
assert certified;
assert #Keys(comp_data) eq 1;
assert #schemes eq 1;
assert Dimension(schemes[1]) eq 2;
M := GradedRingOfHMFs(F, 1);
assert HilbertSeriesSanityCheck(M, NN, schemes);
printf "PASSED (CPU: %os, Wall: %os, Mem: %oMB)\n", Cputime(t0), Time(walltime), GetMemoryUsage() div (1024^2);
