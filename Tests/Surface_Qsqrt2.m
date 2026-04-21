// test-time: ~12m
// HilbertModularVariety end-to-end test: Q(sqrt(2)), level 1
// Known: generators in weights [2,4,6,14], 1 relation in weight 28
// Expected: 1 component (h+ = 1), certified, dimension 2
// Resources: ~16 min CPU, ~791 MB RAM
printf "HilbertModularVariety on Q(sqrt(2)), level 1...";
t0 := Cputime(); walltime := Time();
F := QuadraticField(2);
ZF := Integers(F);
NN := 1*ZF;
comp_data, schemes, certified := HilbertModularVariety(F, NN : MaxB := 30);
assert certified;
assert #Keys(comp_data) eq 1;
assert #schemes eq 1;
assert Dimension(schemes[1]) eq 2;
M := GradedRingOfHMFs(F, 1);
assert HilbertSeriesSanityCheck(M, NN, schemes);
// Check generator weights against Hammond 1973 / Hirzebruch 1977
bb := NarrowClassGroupReps(M)[1];
weights := Sort(&cat[[Weight(f)[1] : f in comp_data[bb][1][k]] : k in Keys(comp_data[bb][1])]);
assert weights eq [2,4,6,14];
printf "PASSED (CPU: %os, Wall: %os, Mem: %oMB)\n", Cputime(t0), Time(walltime), GetMemoryUsage() div (1024^2);
