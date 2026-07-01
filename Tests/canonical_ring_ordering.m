// Regression test for the canonical-ring variable-ordering bug (fixed in f208eb0).
//
// The bug: ConstructWeightedPolynomialRing built the weighted ring in Magma Assoc
// hash-key order, while relation coefficient vectors were computed against a ring
// whose variables were in sorted-by-weight order (Generic(KnownRelations), via
// Sort(Setseq(Keys(Gens))) in ConstructGeneratorsAndRelations). When hash order
// differed from sorted order the two disagreed and the stored equation was scrambled.
//
// Magma's Assoc hashes the integer weight set {2,12} to iteration order [12, 2], which
// is non-ascending, so this set trips the old bug. The fix makes both
// ConstructWeightedPolynomialRing and EvaluateMonomials iterate sorted keys.
//
// On the broken code VariableWeights below is [12, 2] (assert fails) and R.1 evaluates
// to the weight-12 form (assert fails). This is a fast, CI-suitable check: no scheme,
// no Groebner basis, just a weight-2 form and its 6th power.
printf "Canonical ring variable-ordering regression...";

F<nu> := QuadraticField(5);
prec := 100;
R := GradedRingOfHMFs(F, prec);

// Two genuine, distinguishable forms of distinct parallel weight.
E2 := Basis(HMFSpace(R, [2, 2]))[1];
f12 := E2^6;
assert Weight(E2) eq [2, 2];
assert Weight(f12) eq [12, 12];

// Insert the weight-12 key first; the hash iteration order of {2,12} is [12,2]
// regardless of insertion, so this is what would have scrambled the old ring.
Gens := AssociativeArray();
Gens[12] := [f12];
Gens[2] := [E2];
assert [w : w in Keys(Gens)] eq [12, 2]; // confirm hash order is the non-ascending case

// The fix: the weighted polynomial ring must carry variable weights in ascending
// (sorted) order, matching the order relation generation uses.
Rng := ConstructWeightedPolynomialRing(Gens);
weights := VariableWeights(Rng);
assert weights eq [2, 12];
assert weights eq Sort(weights);

// EvaluateMonomials must use the SAME sorted order: R.1 <-> weight 2 <-> E2,
// R.2 <-> weight 12 <-> f12. (Evaluate one monomial per call: a mixed-weight
// SeqEnum of forms has no common universe.)
assert EvaluateMonomials(Gens, [Rng.1])[1] eq E2;
assert EvaluateMonomials(Gens, [Rng.2])[1] eq f12;

printf " Success!\n";
