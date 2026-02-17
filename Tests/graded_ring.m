// Unit tests for the HilbertModularVariety algorithm building blocks:
// HilbertSeriesOfPresentation, AlgebraicallyIndependent, CandidateAlgIndependentElements
// Resources: ~30s, <1 GB RAM

// Test HilbertSeriesOfPresentation
printf "Testing HilbertSeriesOfPresentation...";
F := QuadraticField(13);
ZF := Integers(F);
NN := 1*ZF;
gen_bd := 8;
rel_bd := 2*gen_bd;
prec := ComputePrecisionFromHilbertSeries(NN, gen_bd);
R := GradedRingOfHMFs(F, prec);
dict := ConstructGeneratorsAndRelations(R, NN, gen_bd, rel_bd);
Gens := dict[1];
Rels := dict[2];
// HilbertSeriesOfPresentation should return a rational function
HS := HilbertSeriesOfPresentation(Gens, Rels);
// Cross-check with HilbertSeriesSanityCheck
R_poly := ConstructWeightedPolynomialRing(Gens);
I := ConstructIdeal(R_poly, Rels);
M_check := GradedRingOfHMFs(F, 1);
assert HilbertSeriesSanityCheck(M_check, NN, [I]);
// Also verify the two HS computations agree
assert HS eq HilbertSeries(I);
printf "PASSED\n";


// Test AlgebraicallyIndependent for Q(sqrt(5)) with weight 10 forms
printf "Testing AlgebraicallyIndependent...";
F5 := QuadraticField(5);
ZF5 := Integers(F5);
prec5 := 125;
R5 := GradedRingOfHMFs(F5, prec5);
M10 := HMFSpace(R5, 1*ZF5, [10,10]);
B10 := Basis(M10);
assert #B10 eq 3; // n+1 = 3 for a quadratic field
assert AlgebraicallyIndependent(B10);
printf "PASSED\n";


// Test CandidateAlgIndependentElements
printf "Testing CandidateAlgIndependentElements...";
// Reuse Q(sqrt(13)) gens/rels from above
candidates, found := CandidateAlgIndependentElements(Gens, Rels, 3);
assert found;
assert #candidates eq 3;
printf "PASSED\n";


// Test HilbertModularVariety algorithm on Q(sqrt(13)), level 1
printf "Testing HilbertModularVariety on Q(sqrt(13))...";
F13 := QuadraticField(13);
ZF13 := Integers(F13);
NN13 := 1*ZF13;
comp_data, schemes, certified := HilbertModularVariety(F13, NN13 : MaxB := 30);
// Q(sqrt(13)) has narrow class number 1, so one component
assert #Keys(comp_data) eq 1;
assert #schemes eq 1;
assert certified;
// Verify the Hilbert series independently
M_verify := GradedRingOfHMFs(F13, 1);
bb := NarrowClassGroupReps(M_verify)[1];
Gens13 := comp_data[bb][1];
Rels13 := comp_data[bb][2];
R_poly13 := ConstructWeightedPolynomialRing(Gens13);
I13 := ConstructIdeal(R_poly13, Rels13);
assert HilbertSeriesSanityCheck(M_verify, NN13, [I13]);
// Check that the scheme has dimension 2 (it's a surface)
assert Dimension(schemes[1]) eq 2;
printf "PASSED\n";
