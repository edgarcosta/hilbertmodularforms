// HilbertModularVariety end-to-end test: Q(sqrt(13)), level pp (norm 3)
// 3 splits in Q(sqrt(13)): 3*ZF = pp * ppbar, each of norm 3
// Expected: 1 component, certified, dimension 2
// Resources: ~23s CPU, ~140 MB RAM
printf "HilbertModularVariety on Q(sqrt(13)), level pp (norm 3)...";
t0 := Cputime(); walltime := Time();
F := QuadraticField(13);
ZF := Integers(F);
pp := Factorization(3*ZF)[1][1];
comp_data, schemes, certified := HilbertModularVariety(F, pp : MaxB := 20);
assert certified;
assert #Keys(comp_data) eq 1;
assert #schemes eq 1;
assert Dimension(schemes[1]) eq 2;
M := GradedRingOfHMFs(F, 1);
assert HilbertSeriesSanityCheck(M, pp, schemes);
printf "PASSED (CPU: %os, Wall: %os, Mem: %oMB)\n", Cputime(t0), Time(walltime), GetMemoryUsage() div (1024^2);
