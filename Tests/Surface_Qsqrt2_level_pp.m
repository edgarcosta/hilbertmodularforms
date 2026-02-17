// HilbertModularVariety end-to-end test: Q(sqrt(2)), level pp (norm 2)
// pp is the unique prime above 2, with pp^2 = 2*ZF
// Known: generators in weights [2,2,4,10], 1 relation in weight 20
// Expected: 1 component, certified, dimension 2
// Resources: >10 min CPU (estimated)
printf "HilbertModularVariety on Q(sqrt(2)), level pp (norm 2)...";
t0 := Cputime(); walltime := Time();
F := QuadraticField(2);
ZF := Integers(F);
pp := Factorization(2*ZF)[1][1];
comp_data, schemes, certified := HilbertModularVariety(F, pp : MaxB := 20);
assert certified;
assert #Keys(comp_data) eq 1;
assert #schemes eq 1;
assert Dimension(schemes[1]) eq 2;
M := GradedRingOfHMFs(F, 1);
assert HilbertSeriesSanityCheck(M, pp, schemes);
printf "PASSED (CPU: %os, Wall: %os, Mem: %oMB)\n", Cputime(t0), Time(walltime), GetMemoryUsage() div (1024^2);
