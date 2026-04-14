// Test: surface invariants cross-check with canonical ring computation
// Verifies ArithmeticGenus, ChernNumbers, GeometricGenus, Irregularity
// are consistent across computation paths and with known values
// Resources: ~20s CPU, <200 MB RAM
printf "Surface invariants vs canonical ring...";
t0 := Cputime(); walltime := Time();

// === Q(sqrt(13)), level 1 ===
// Known: chi = 1 (from van der Geer tables)
F13 := QuadraticField(13);
ZF13 := Integers(F13);
NN13 := 1*ZF13;

// Test ArithmeticGenus from two code paths
chi_field := ArithmeticGenus(F13);  // IntersectionRing.m path (via ChernNumbers of ChowRing)
Gamma13 := Gamma0(F13, NN13);
chi_group := ArithmeticGenus(Gamma13);  // SurfaceInvariants.m path (via K2+EulerNumber)
assert chi_field eq chi_group;
assert chi_field eq 1;

// Noether formula: c1^2 + c2 = 12*chi
c12, c2 := ChernNumbers(Gamma13);
assert c12 + c2 eq 12*chi_field;

// GeometricGenus = chi - 1, Irregularity = 0 (always for HMS)
assert GeometricGenus(Gamma13) eq chi_field - 1;
assert Irregularity(Gamma13) eq 0;

// The canonical ring should be certified and have matching Hilbert series
comp_data, schemes, certified := HilbertModularVariety(F13, NN13 : MaxB := 20);
assert certified;
M := GradedRingOfHMFs(F13, 1);
assert HilbertSeriesSanityCheck(M, NN13, schemes);

// === Q(sqrt(5)), level 1 ===
// Known: chi = 1 (Gundlach 1963)
F5 := QuadraticField(5);
ZF5 := Integers(F5);
NN5 := 1*ZF5;
chi5_field := ArithmeticGenus(F5);
Gamma5 := Gamma0(F5, NN5);
chi5_group := ArithmeticGenus(Gamma5);
assert chi5_field eq chi5_group;
assert chi5_field eq 1;
c12_5, c2_5 := ChernNumbers(Gamma5);
assert c12_5 + c2_5 eq 12*chi5_field;
assert GeometricGenus(Gamma5) eq 0;
assert Irregularity(Gamma5) eq 0;

// === Q(sqrt(29)), level 1 ===
// Known: chi = 2 (invariants only, no ring computation)
F29 := QuadraticField(29);
ZF29 := Integers(F29);
NN29 := 1*ZF29;
chi29 := ArithmeticGenus(F29);
Gamma29 := Gamma0(F29, NN29);
assert chi29 eq ArithmeticGenus(Gamma29);
assert chi29 eq 2;
c12_29, c2_29 := ChernNumbers(Gamma29);
assert c12_29 + c2_29 eq 12*chi29;
assert GeometricGenus(Gamma29) eq 1;
assert Irregularity(Gamma29) eq 0;

// === Q(sqrt(13)), level pp (norm 3) ===
// Nontrivial level: just check Noether formula consistency
F := F13;
ZF := ZF13;
fac := Factorization(3*ZF);
pp := fac[1][1];
Gamma_pp := Gamma0(F, pp);
chi_pp := ArithmeticGenus(Gamma_pp);
c12_pp, c2_pp := ChernNumbers(Gamma_pp);
assert c12_pp + c2_pp eq 12*chi_pp;
assert GeometricGenus(Gamma_pp) eq chi_pp - 1;
assert Irregularity(Gamma_pp) eq 0;

printf "PASSED (CPU: %os, Wall: %os, Mem: %oMB)\n", Cputime(t0), Time(walltime), GetMemoryUsage() div (1024^2);
