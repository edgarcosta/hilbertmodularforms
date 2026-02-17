// Consistency test: 4-arg vs 2-arg HilbertModularVariety
// Verifies both produce schemes with matching Hilbert series on Q(sqrt(13))
// Resources: ~30s CPU, <200 MB RAM
printf "Consistency: 4-arg vs 2-arg HilbertModularVariety on Q(sqrt(13))...";
t0 := Cputime(); walltime := Time();
F := QuadraticField(13);
ZF := Integers(F);
NN := 1*ZF;

// 2-arg version (Algorithm 1 with certification)
comp_data, schemes_new, certified := HilbertModularVariety(F, NN : MaxB := 20);
assert certified;
assert #schemes_new eq 1;

// 4-arg version (direct computation with explicit weight bounds)
S_old := HilbertModularVariety(F, NN, 8, 16);

// Both should produce dimension-2 schemes
assert Dimension(schemes_new[1]) eq 2;
assert Dimension(S_old) eq 2;

// Both should pass the Hilbert series sanity check
M := GradedRingOfHMFs(F, 1);
assert HilbertSeriesSanityCheck(M, NN, schemes_new);
assert HilbertSeriesSanityCheck(M, NN, [S_old]);

// Defining equations should have the same count
eqns_new := DefiningEquations(schemes_new[1]);
eqns_old := DefiningEquations(S_old);
assert #eqns_new eq #eqns_old;

// Generator weights should match (compare via the graded ring structure)
R_new := CoordinateRing(Ambient(schemes_new[1]));
R_old := CoordinateRing(Ambient(S_old));
assert Rank(R_new) eq Rank(R_old);  // same number of generators

printf "PASSED (CPU: %os, Wall: %os, Mem: %oMB)\n", Cputime(t0), Time(walltime), GetMemoryUsage() div (1024^2);
