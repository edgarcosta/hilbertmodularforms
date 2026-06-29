// Regression: the unified HilbertModularVariety must agree between its two modes
// on Q(sqrt(13)) (narrow class number 1): explicit weight bounds (GeneratorWeight
// set) vs the B-search (GeneratorWeight unset). Replaces the old 4-arg-vs-2-arg
// consistency test now that both are one intrinsic.
printf "HilbertModularVariety explicit-bounds vs search on Q(sqrt(13))...";
F := QuadraticField(13);
ZF := Integers(F);
NN := 1*ZF;

// Search mode (Algorithm 1 with certification)
comp_data, schemes_search, certified := HilbertModularVariety(F, NN : MaxB := 20);
assert certified;
assert #schemes_search eq 1;
assert Dimension(schemes_search[1]) eq 2;

// Explicit-bounds mode (formerly the 4-arg overload)
comp_data2, schemes_expl, cert2 := HilbertModularVariety(F, NN : GeneratorWeight := 8, RelationWeight := 16);
// Explicit-bounds mode returns certified = false (it performs no Jacobian certification).
// This is the distinguisher that GATES the branch: if an implementer adds the parameters but
// forgets the explicit-bounds branch, the search path runs instead and returns certified = true,
// so this single assertion fails. The Hilbert-series checks below would pass either way.
assert not cert2;
assert #schemes_expl eq 1;
assert Dimension(schemes_expl[1]) eq 2;

// Both presentations must define the same Hilbert series and pass the sanity check
M := GradedRingOfHMFs(F, 1);
assert HilbertSeriesSanityCheck(M, NN, schemes_search);
assert HilbertSeriesSanityCheck(M, NN, schemes_expl);
assert HilbertSeries(Ideal(schemes_search[1])) eq HilbertSeries(Ideal(schemes_expl[1]));

printf "PASSED\n";
