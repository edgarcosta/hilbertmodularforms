// Verify precomputed canonical ring equations from Verification/CanonicalRingEquations/
// against trace formula Hilbert series.
// For each file, we eval the equation file (which defines a Scheme S),
// then check that HilbertSeriesSanityCheck passes.
// These tests are purely algebraic (no HMF basis computation), so they run quickly.
// Resources: ~60s, <2 GB RAM
//
// Files for D=12,21,24,28,33 are NOT tested here because they have narrow class
// number > 1 and their regeneration hits the upstream Magma bug at
// precompute.m:1064 (definite method).


// === Q(sqrt(5)), level 1 [disc=5, label 2.2.5.1-1.1] ===
printf "Verifying Q(sqrt(5)) level 1...";
I := eval (Read("Verification/CanonicalRingEquations/2.2.5.1-1.1-gl-0.m") cat "return Ideal(S);");
F5 := LMFDBField("2.2.5.1"); ZF5 := Integers(F5);
M5 := GradedRingOfHMFs(F5, 1);
assert HilbertSeriesSanityCheck(M5, 1*ZF5, [I]);
printf "PASSED\n";


// === Q(sqrt(5)), level 4.1 [disc=5, label 2.2.5.1-4.1] ===
printf "Verifying Q(sqrt(5)) level 4.1...";
I := eval (Read("Verification/CanonicalRingEquations/2.2.5.1-4.1-gl-0.m") cat "return Ideal(S);");
NN5_4 := LMFDBIdeal(F5, "4.1");
assert HilbertSeriesSanityCheck(M5, NN5_4, [I]);
printf "PASSED\n";


// === Q(sqrt(5)), level 5.1 [disc=5, label 2.2.5.1-5.1] ===
printf "Verifying Q(sqrt(5)) level 5.1...";
I := eval (Read("Verification/CanonicalRingEquations/2.2.5.1-5.1-gl-0.m") cat "return Ideal(S);");
NN5_5 := LMFDBIdeal(F5, "5.1");
assert HilbertSeriesSanityCheck(M5, NN5_5, [I]);
printf "PASSED\n";


// === Q(sqrt(2)), level 1 [disc=8, label 2.2.8.1-1.1] ===
printf "Verifying Q(sqrt(2)) level 1...";
I := eval (Read("Verification/CanonicalRingEquations/2.2.8.1-1.1-gl-0.m") cat "return Ideal(S);");
F2 := LMFDBField("2.2.8.1"); ZF2 := Integers(F2);
M8 := GradedRingOfHMFs(F2, 1);
assert HilbertSeriesSanityCheck(M8, 1*ZF2, [I]);
printf "PASSED\n";


// === Q(sqrt(2)), level 2.1 [disc=8, label 2.2.8.1-2.1] ===
printf "Verifying Q(sqrt(2)) level 2.1...";
I := eval (Read("Verification/CanonicalRingEquations/2.2.8.1-2.1-gl-0.m") cat "return Ideal(S);");
NN8_2 := LMFDBIdeal(F2, "2.1");
assert HilbertSeriesSanityCheck(M8, NN8_2, [I]);
printf "PASSED\n";


// === Q(sqrt(13)), level 1 [disc=13, label 2.2.13.1-1.1] ===
printf "Verifying Q(sqrt(13)) level 1...";
I13_ref := eval (Read("Verification/CanonicalRingEquations/2.2.13.1-1.1-gl-0.m") cat "return Ideal(S);");
F13 := LMFDBField("2.2.13.1"); ZF13 := Integers(F13);
M13 := GradedRingOfHMFs(F13, 1);
assert HilbertSeriesSanityCheck(M13, 1*ZF13, [I13_ref]);
printf "PASSED\n";


// === Q(sqrt(13)), level 3.1 [disc=13, label 2.2.13.1-3.1] ===
printf "Verifying Q(sqrt(13)) level 3.1...";
I := eval (Read("Verification/CanonicalRingEquations/2.2.13.1-3.1-gl-0.m") cat "return Ideal(S);");
NN13_3 := LMFDBIdeal(F13, "3.1");
assert HilbertSeriesSanityCheck(M13, NN13_3, [I]);
printf "PASSED\n";


// === Q(sqrt(13)), level 4.1 [disc=13, label 2.2.13.1-4.1] ===
printf "Verifying Q(sqrt(13)) level 4.1...";
I := eval (Read("Verification/CanonicalRingEquations/2.2.13.1-4.1-gl-0.m") cat "return Ideal(S);");
NN13_4 := LMFDBIdeal(F13, "4.1");
assert HilbertSeriesSanityCheck(M13, NN13_4, [I]);
printf "PASSED\n";


// === Q(sqrt(17)), level 1 [disc=17, label 2.2.17.1-1.1] ===
printf "Verifying Q(sqrt(17)) level 1...";
I := eval (Read("Verification/CanonicalRingEquations/2.2.17.1-1.1-gl-0.m") cat "return Ideal(S);");
F17 := LMFDBField("2.2.17.1"); ZF17 := Integers(F17);
M17 := GradedRingOfHMFs(F17, 1);
assert HilbertSeriesSanityCheck(M17, 1*ZF17, [I]);
printf "PASSED\n";


// === Q(sqrt(29)), level 1 [disc=29, label 2.2.29.1-1.1] ===
printf "Verifying Q(sqrt(29)) level 1...";
I := eval (Read("Verification/CanonicalRingEquations/2.2.29.1-1.1-gl-0.m") cat "return Ideal(S);");
F29 := LMFDBField("2.2.29.1"); ZF29 := Integers(F29);
M29 := GradedRingOfHMFs(F29, 1);
assert HilbertSeriesSanityCheck(M29, 1*ZF29, [I]);
printf "PASSED\n";


// === Q(sqrt(37)), level 1 [disc=37, label 2.2.37.1-1.1] ===
printf "Verifying Q(sqrt(37)) level 1...";
I := eval (Read("Verification/CanonicalRingEquations/2.2.37.1-1.1-gl-0.m") cat "return Ideal(S);");
F37 := LMFDBField("2.2.37.1"); ZF37 := Integers(F37);
M37 := GradedRingOfHMFs(F37, 1);
assert HilbertSeriesSanityCheck(M37, 1*ZF37, [I]);
printf "PASSED\n";


// === Q(sqrt(41)), level 1 [disc=41, label 2.2.41.1-1.1] ===
printf "Verifying Q(sqrt(41)) level 1...";
I := eval (Read("Verification/CanonicalRingEquations/2.2.41.1-1.1-gl-0.m") cat "return Ideal(S);");
F41 := LMFDBField("2.2.41.1"); ZF41 := Integers(F41);
M41 := GradedRingOfHMFs(F41, 1);
assert HilbertSeriesSanityCheck(M41, 1*ZF41, [I]);
printf "PASSED\n";


// === Cross-check: run HilbertModularVariety on Q(sqrt(13)) ===
// Verify the output matches the stored reference equations
printf "Cross-checking HilbertModularVariety output vs reference for Q(sqrt(13))...";
comp_data, schemes, certified := HilbertModularVariety(F13, 1*ZF13 : MaxB := 30);
assert certified;
assert #schemes eq 1;
assert Dimension(schemes[1]) eq 2;
// The Hilbert series of the HilbertModularVariety output should match the reference
assert HilbertSeriesSanityCheck(M13, 1*ZF13, schemes);
// Also verify it matches the stored reference
assert HilbertSeries(Ideal(schemes[1])) eq HilbertSeries(I13_ref);
printf "PASSED\n";
