// test-time: ~18m
// HilbertModularVariety end-to-end test: Q(sqrt(5)), level 2*ZF
// 2 is inert in Q(sqrt(5)), so 2*ZF is a prime ideal of norm 4
// Expected: 1 component, certified, dimension 2
// Resources: ~33 min CPU, ~1135 MB RAM
printf "HilbertModularVariety on Q(sqrt(5)), level 2*ZF...";
t0 := Cputime(); walltime := Time();
F := QuadraticField(5);
ZF := Integers(F);
NN := 2*ZF;
comp_data, schemes, certified := HilbertModularVariety(F, NN : MaxB := 20);
assert certified;
assert #Keys(comp_data) eq 1;
assert #schemes eq 1;
assert Dimension(schemes[1]) eq 2;
M := GradedRingOfHMFs(F, 1);
assert HilbertSeriesSanityCheck(M, NN, schemes);
printf "PASSED (CPU: %os, Wall: %os, Mem: %oMB)\n", Cputime(t0), Time(walltime), GetMemoryUsage() div (1024^2);
