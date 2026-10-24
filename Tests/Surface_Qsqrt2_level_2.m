// test-time: ~2m
// HilbertModularVariety end-to-end test: Q(sqrt(2)), level 2*ZF
// 2*ZF = pp^2 where pp is the prime above 2
// Known: generators in weights [2,2,2,8], 1 relation in weight 16
// Literature: van der Geer 1988 (Hilbert Modular Surfaces), VIII.2.8-2.10 pp.194-195,
// gives the ring of the principal subgroup Gamma[2] of this level. Compare the even
// part of its invariants under Gamma0(2)/Gamma[2].
// Expected: 1 component, certified, dimension 2
// Resources: ~3 min CPU, ~384 MB RAM
printf "HilbertModularVariety on Q(sqrt(2)), level 2*ZF...";
t0 := Cputime(); walltime := Time();
F := QuadraticField(2);
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
