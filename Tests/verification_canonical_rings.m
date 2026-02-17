// Verify precomputed canonical ring equations from Verification/CanonicalRingEquations/
// against trace formula Hilbert series.
// These tests are purely algebraic (no HMF basis computation), so they run quickly.
// Resources: ~15s, <1 GB RAM

// Helper: construct ideal from a weighted polynomial ring and equation list
function IdealFromEqns(weights, eqns_func)
  R := PolynomialRing(RationalField(), weights, <"grevlexw", weights>);
  eqns := eqns_func(R);
  I := ideal<R | eqns>;
  return I;
end function;


// Test Q(sqrt(13)), level 1 [disc=13, label 2.2.13.1-1.1]
// Generators in weight: 2,4,6,6,8; Relations in weight: 12,16
printf "Verifying Q(sqrt(13)) level 1 equations...";
I13 := IdealFromEqns([2, 4, 6, 6, 8], func<R |
[
R.2^3 - R.1*R.2*R.4 - 4*R.3*R.4 + 4*R.4^2,
R.1^4*R.2^2 - 4*R.1^3*R.2*R.3 - 416*R.1*R.2^2*R.3 + 16*R.1^2*R.3^2 + 3456*R.2*R.3^2 - R.1^5*R.4 + 4*R.1^3*R.2*R.4 + 268*R.1*R.2^2*R.4 + 384*R.1^2*R.3*R.4 - 2928*R.2*R.3*R.4 - 252*R.1^2*R.4^2 + 1200*R.2*R.4^2 + 112*R.2^2*R.5 - 64*R.1*R.3*R.5 - 112*R.1*R.4*R.5 + 64*R.5^2
]>);
F13 := QuadraticField(13);
ZF13 := Integers(F13);
M13 := GradedRingOfHMFs(F13, 1);
assert HilbertSeriesSanityCheck(M13, 1*ZF13, [I13]);
printf "PASSED\n";


// Test Q(sqrt(2)), level 1 [disc=8, label 2.2.8.1-1.1]
// Generators in weight: 2,4,6,14; Relations in weight: 28
printf "Verifying Q(sqrt(2)) level 1 equations...";
I8 := IdealFromEqns([2, 14, 4, 6], func<R |
[
276*R.1*R.2*R.3^3 + 80*R.1^2*R.3^6 - 20*R.3^7 + R.1^2*R.2*R.3*R.4 + 1124*R.2*R.3^2*R.4 + 740*R.1*R.3^5*R.4 - 2*R.1*R.2*R.4^2 - R.1^2*R.3^3*R.4^2 + 1728*R.3^4*R.4^2 - 2*R.1*R.3^2*R.4^3 + R.1^2*R.4^4 + R.3*R.4^4
]>);
F2 := QuadraticField(2);
ZF2 := Integers(F2);
M8 := GradedRingOfHMFs(F2, 1);
assert HilbertSeriesSanityCheck(M8, 1*ZF2, [I8]);
printf "PASSED\n";


// Test Q(sqrt(5)), level 1 [disc=5, label 2.2.5.1-1.1]
// Generators in weight: 2,6,20,10; Relations in weight: 40
printf "Verifying Q(sqrt(5)) level 1 equations...";
I5 := IdealFromEqns([2, 6, 20, 10], func<R |
[
R.1^2*R.2^6 + 3*R.1^4*R.2^2*R.3 - 1696*R.1*R.2^3*R.3 - 47296*R.3^2 - 3*R.1^3*R.2^4*R.4 + 864*R.2^5*R.4 - R.1^5*R.3*R.4 + 896*R.1^2*R.2*R.3*R.4 - 16*R.1*R.2^3*R.4^2 - 832*R.3*R.4^2 + 16*R.1^2*R.2*R.4^3 + 64*R.4^4
]>);
F5 := QuadraticField(5);
ZF5 := Integers(F5);
M5 := GradedRingOfHMFs(F5, 1);
assert HilbertSeriesSanityCheck(M5, 1*ZF5, [I5]);
printf "PASSED\n";


// Test Q(sqrt(17)), level 1 [disc=17, label 2.2.17.1-1.1]
// Generators in weight: 2,4,4,6,6,6,8; Relations in weight: 10,12,12,12,12,12,14,14,16
printf "Verifying Q(sqrt(17)) level 1 equations...";
I17 := IdealFromEqns([2, 4, 4, 6, 6, 6, 8], func<R |
[
2*R.3^3 + R.1*R.3*R.5 - R.4*R.5 + 2*R.5^2 + R.5*R.6 - R.3*R.7,
2*R.2*R.3^2 + R.1*R.3*R.6 - R.4*R.6 + 2*R.5*R.6 + R.6^2 - R.2*R.7,
R.2^2*R.3 + R.3^3 - R.4*R.6 - 2*R.5*R.6 + R.6^2 - R.2*R.7,
-R.2^3 + R.2^2*R.3 - R.2*R.3^2 - R.3^3 + R.1*R.2*R.6 + R.4*R.6 + 2*R.5*R.6 + 3*R.6^2 + R.2*R.7,
-R.1^2*R.2^2 + 4*R.2^3 + 2*R.1^2*R.2*R.3 - 2*R.2^2*R.3 - R.1^2*R.3^2 - 10*R.2*R.3^2 - 104*R.3^3 + 4*R.1*R.3*R.4 - 4*R.4^2 + 33*R.1*R.3*R.5 - 25*R.4*R.5 + 66*R.5^2 + R.1^3*R.6 + 17*R.1*R.3*R.6 - 27*R.4*R.6 - 25*R.5*R.6 - R.6^2 - 31*R.2*R.7 - 41*R.3*R.7,
-R.2^2*R.4 + 2*R.2*R.3*R.4 - R.3^2*R.4 + 2*R.3^2*R.5 + R.2^2*R.6 + 5*R.3^2*R.6 + R.1*R.4*R.6 + 2*R.1*R.5*R.6 - R.1*R.6^2 - 4*R.6*R.7,
-8*R.2^2*R.4 + R.1^2*R.3*R.4 + 16*R.2*R.3*R.4 - 16*R.3^2*R.4 - R.1*R.4^2 + 21*R.1^2*R.3*R.5 - 184*R.3^2*R.5 - 20*R.1*R.4*R.5 + 44*R.1*R.5^2 + 4*R.2^2*R.6 + 8*R.1^2*R.3*R.6 - 16*R.2*R.3*R.6 + 20*R.3^2*R.6 + R.1*R.4*R.6 + 46*R.1*R.5*R.6 + 4*R.1*R.6^2 - 8*R.1*R.2*R.7 - 24*R.1*R.3*R.7 + 4*R.4*R.7 - 8*R.5*R.7 - 32*R.6*R.7,
2*R.3*R.4^2 + 50*R.3*R.4*R.5 + R.1^2*R.5^2 + 108*R.3*R.5^2 - R.1*R.2^2*R.6 - R.1*R.3^2*R.6 + 2*R.2*R.4*R.6 + 10*R.3*R.4*R.6 - 18*R.3*R.5*R.6 + R.1^2*R.6^2 + 2*R.2*R.6^2 + 8*R.3*R.6^2 + R.2^2*R.7 + 14*R.2*R.3*R.7 + 41*R.3^2*R.7 - R.1*R.4*R.7 - 2*R.1*R.5*R.7 + R.1*R.6*R.7 + 4*R.7^2,
R.2*R.5 - R.3*R.6
]>);
F17 := QuadraticField(17);
ZF17 := Integers(F17);
M17 := GradedRingOfHMFs(F17, 1);
assert HilbertSeriesSanityCheck(M17, 1*ZF17, [I17]);
printf "PASSED\n";


// Test Q(sqrt(2)), level pp (norm 2) [disc=8, label 2.2.8.1-2.1]
// pp is the unique prime above 2 with pp^2 = 2*ZF
// Generators in weight: 2,2,4,10; Relations in weight: 20
printf "Verifying Q(sqrt(2)) level pp (norm 2) equations...";
I8_pp := IdealFromEqns([2, 2, 4, 10], func<R |
[
R.1^10 - 11638/463*R.1^9*R.2 + 113859/463*R.1^8*R.2^2 - 561288/463*R.1^7*R.2^3 + 1538382/463*R.1^6*R.2^4 - 2469636/463*R.1^5*R.2^5 + 2316558/463*R.1^4*R.2^6 - 1146504/463*R.1^3*R.2^7 + 157923/463*R.1^2*R.2^8 + 93578/463*R.1*R.2^9 - 31697/463*R.2^10 + 2160576/463*R.1^8*R.3 - 36278784/463*R.1^7*R.2*R.3 + 218006784/463*R.1^6*R.2^2*R.3 - 619402752/463*R.1^5*R.2^3*R.3 + 945429120/463*R.1^4*R.2^4*R.3 - 799059456/463*R.1^3*R.2^5*R.3 + 349887744/463*R.1^2*R.2^6*R.3 - 58673664/463*R.1*R.2^7*R.3 - 2069568/463*R.2^8*R.3 + 605076480/463*R.1^6*R.3^2 - 365783040/463*R.1^5*R.2*R.3^2 - 35339369472/463*R.1^4*R.2^2*R.3^2 + 132913778688/463*R.1^3*R.2^3*R.3^2 - 192123436032/463*R.1^2*R.2^4*R.3^2 + 125061470208/463*R.1*R.2^5*R.3^2 - 30751736832/463*R.2^6*R.3^2 - 5165895647232/463*R.1^4*R.3^3 + 42807066624000/463*R.1^3*R.2*R.3^3 - 97425825988608/463*R.1^2*R.2^2*R.3^3 + 87094034694144/463*R.1*R.2^3*R.3^3 - 27309379682304/463*R.2^4*R.3^3 - 4346654006181888/463*R.1^2*R.3^4 + 10891291885830144/463*R.1*R.2*R.3^4 - 7559091975094272/463*R.2^2*R.3^4 + 445906944/463*R.1^5*R.4 - 5287182336/463*R.1^4*R.2*R.4 + 16689659904/463*R.1^3*R.2^2*R.4 - 22804955136/463*R.1^2*R.2^3*R.4 + 14460125184/463*R.1*R.2^4*R.4 - 3503554560/463*R.2^5*R.4 - 1779550912512/463*R.1^3*R.3*R.4 + 7099857764352/463*R.1^2*R.2*R.3*R.4 + 12273397530624/463*R.1*R.2^2*R.3*R.4 - 17593704382464/463*R.2^3*R.3*R.4 - 3212437968912384/463*R.1*R.3^2*R.4 + 1183529778020352/463*R.2*R.3^2*R.4 - 1014454095446016/463*R.4^2
]>);
F2b := QuadraticField(2);
ZF2b := Integers(F2b);
// The prime above 2 in Q(sqrt(2)): (sqrt(2)) with norm 2
pp2 := Factorization(2*ZF2b)[1][1];
M8b := GradedRingOfHMFs(F2b, 1);
assert HilbertSeriesSanityCheck(M8b, pp2, [I8_pp]);
printf "PASSED\n";


// Cross-check: run HilbertModularVariety on Q(sqrt(13)) and verify the output Hilbert series
// matches the reference equations above
printf "Cross-checking HilbertModularVariety output vs reference for Q(sqrt(13))...";
comp_data, schemes, certified := HilbertModularVariety(F13, 1*ZF13 : MaxB := 30);
assert certified;
assert #schemes eq 1;
assert Dimension(schemes[1]) eq 2;
// The Hilbert series of the HilbertModularVariety output should match the reference
assert HilbertSeriesSanityCheck(M13, 1*ZF13, schemes);
// Also verify it matches the stored reference
assert HilbertSeries(Ideal(schemes[1])) eq HilbertSeries(I13);
printf "PASSED\n";
