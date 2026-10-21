// HilbertModularVariety end-to-end test: Q(sqrt(3)), disc=12, level 1
// Multi-component: narrow class number h+ = 2
// Each component has gens [2,14,4,6] (same structure as Q(sqrt(2)))
// Literature: van der Geer 1988 (Hilbert Modular Surfaces), VIII.2.13 p.197: even ring for
// PSL2(O) on H x H, weights [2,4,6,6,8]. Our H x H component is its invariant subring under
// (z1,z2) -> (eps z1, eps' z2), eps = 2+sqrt3; the other component is H x H^- (VIII.2.14).
// Expected: 2 components, certified, each dimension 2
// Resources: >4 hours CPU (timed out at 4h)
// EXCLUDED FROM CI: exceeds reasonable CI time limits
printf "HilbertModularVariety on Q(sqrt(3)) (disc=12), level 1 (h+=2)...";
t0 := Cputime(); walltime := Time();
F := QuadraticField(3);
ZF := Integers(F);
NN := 1*ZF;
comp_data, schemes, certified := HilbertModularVariety(F, NN : MaxB := 30);
assert certified;
assert #Keys(comp_data) eq 2;
assert #schemes eq 2;
for i in [1..#schemes] do
  assert Dimension(schemes[i]) eq 2;
end for;
M := GradedRingOfHMFs(F, 1);
assert HilbertSeriesSanityCheck(M, NN, schemes);
printf "PASSED (CPU: %os, Wall: %os, Mem: %oMB)\n", Cputime(t0), Time(walltime), GetMemoryUsage() div (1024^2);
