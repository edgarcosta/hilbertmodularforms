// HilbertModularVariety end-to-end test: Q(sqrt(21)), level 1
// Multi-component: narrow class number h+ = 2
// Component 1 gens: [2,4,6,6,8], Component 2 gens: [2,4,4,6,10]
// Expected: 2 components, certified, each dimension 2
// Resources: >10 min CPU, ~5 GB RAM (estimated)
printf "HilbertModularVariety on Q(sqrt(21)), level 1 (h+=2)...";
t0 := Cputime(); walltime := Time();
F := QuadraticField(21);
ZF := Integers(F);
NN := 1*ZF;
comp_data, schemes, certified := HilbertModularVariety(F, NN : MaxB := 20);
assert certified;
assert #Keys(comp_data) eq 2;
assert #schemes eq 2;
for i in [1..#schemes] do
  assert Dimension(schemes[i]) eq 2;
end for;
M := GradedRingOfHMFs(F, 1);
assert HilbertSeriesSanityCheck(M, NN, schemes);
printf "PASSED (CPU: %os, Wall: %os, Mem: %oMB)\n", Cputime(t0), Time(walltime), GetMemoryUsage() div (1024^2);
