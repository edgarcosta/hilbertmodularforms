// HilbertModularVariety end-to-end test: Q(sqrt(33)), level 1
// Multi-component: narrow class number h+ = 2
// Expected: 2 components, certified, each dimension 2
// Resources: >10 min CPU (estimated)
// EXCLUDED FROM CI: precompute.m L1070 row-sum assertion fails for h+=2
// fields. "assert &+[#tps[<j,i>]] eq num" -- Hecke-neighbour enumeration
// in precompute_tps misses elements when the narrow class group is
// non-trivial and prime P is in support of right-ideal classes.
printf "HilbertModularVariety on Q(sqrt(33)), level 1 (h+=2)...";
t0 := Cputime(); walltime := Time();
F := QuadraticField(33);
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
