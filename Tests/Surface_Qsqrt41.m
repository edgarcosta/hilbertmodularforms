// HilbertModularVariety end-to-end test: Q(sqrt(41)), level 1
// Expected: 1 component (h+ = 1), certified, dimension 2
// Resources: >10 min CPU (estimated)
printf "HilbertModularVariety on Q(sqrt(41)), level 1...";
t0 := Cputime(); walltime := Time();
F := QuadraticField(41);
ZF := Integers(F);
NN := 1*ZF;
comp_data, schemes, certified := HilbertModularVariety(F, NN : MaxB := 20);
assert certified;
assert #Keys(comp_data) eq 1;
assert #schemes eq 1;
assert Dimension(schemes[1]) eq 2;
M := GradedRingOfHMFs(F, 1);
assert HilbertSeriesSanityCheck(M, NN, schemes);
printf "PASSED (CPU: %os, Wall: %os, Mem: %oMB)\n", Cputime(t0), Time(walltime), GetMemoryUsage() div (1024^2);
