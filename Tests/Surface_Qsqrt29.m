// HilbertModularVariety end-to-end test: Q(sqrt(29)), level 1
// Known: generators in weights [2,2,4,6,6,6,8], many relations
// Expected: 1 component (h+ = 1), certified, dimension 2
// Resources: >10 min CPU, ~3 GB RAM (estimated)
printf "HilbertModularVariety on Q(sqrt(29)), level 1...";
t0 := Cputime(); walltime := Time();
F := QuadraticField(29);
ZF := Integers(F);
NN := 1*ZF;
comp_data, schemes, certified := HilbertModularVariety(F, NN : MaxB := 20);
assert certified;
assert #Keys(comp_data) eq 1;
assert #schemes eq 1;
assert Dimension(schemes[1]) eq 2;
M := GradedRingOfHMFs(F, 1);
assert HilbertSeriesSanityCheck(M, NN, schemes);
// Check generator weights against Williams 2020
bb := NarrowClassGroupReps(M)[1];
weights := Sort(&cat[[Weight(f)[1] : f in comp_data[bb][1][k]] : k in Keys(comp_data[bb][1])]);
assert weights eq [2,2,4,6,6,6,8];
printf "PASSED (CPU: %os, Wall: %os, Mem: %oMB)\n", Cputime(t0), Time(walltime), GetMemoryUsage() div (1024^2);
