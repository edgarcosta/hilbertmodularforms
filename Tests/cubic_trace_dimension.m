// test-time: ~15s
//
// Focused regression: the trace-formula dimension for a cubic field must be an integer and
// agree with the builtin backend, computed through the trace path itself (not a fallback).
// Broader multi-field / Hecke / residue-degree coverage lives in Tests/cubic_dimension_battery.m.
//
// The Eichler-Selberg trace formula in ModFrmHilD/Trace/Trace.m was only ever validated for
// real quadratic fields (see Tests/dimensions.m, Tests/traces.m, and pos_elts_of_trace.m
// which asserts Degree(F) eq 2). Its nonprecomp local optimal-embedding count
// (EmbeddingNumberOverUnitIndex) was wrong at even inert primes of odd residue degree: for
// F = Q(zeta_7)^+ (disc 49) the prime 2 is inert with residue field F_8, and the old
// root-counting OptimalEmbeddingNumber returned 0 instead of 1 + (K/pp) = 2. So
// Trace(: precomp := false) gave the non-integer cusp "dimensions" 6/7 and 22/7 at weights
// 2 and 4, and on that broken backend CuspDimension(: version := "trace") and
// ComputePrecisionFromHilbertSeries threw. The builtin backend gives dim M_2 = 2, dim M_4 = 6.
//
// The fix rewires the nonprecomp path to the same Hijikata closed form (OptimalEmbeddings)
// already used by the precomp path, so the trace path is integer-valued and agrees with
// builtin for degree > 2.

Qx<x> := PolynomialRing(Rationals());
F := NumberField(x^3 - x^2 - 2*x + 1); // Q(zeta_7)^+, disc 49
ZF := Integers(F);
NN := 2*ZF;

assert Degree(F) eq 3;
assert Discriminant(ZF) eq 49;
assert NarrowClassNumber(F) eq 1; // rules out class-group-character effects

R := GradedRingOfHMFs(F, 1);

// Known-correct dimensions (Magma builtin, cross-checked against arXiv:2501.15719
// Table tab:positive-kod for the D=49 level-(2) target).
expected_cusp := AssociativeArray();
expected_cusp[2] := 0;
expected_cusp[4] := 4;
expected_total := AssociativeArray();
expected_total[2] := 2;
expected_total[4] := 6;

for k in [2, 4] do
    Mk := HMFSpace(R, NN, [k, k, k]);

    // Default CuspDimension path uses version := "trace"; on the broken backend this threw
    // for the cubic field. After the fix the trace path itself is integer-valued and must
    // match builtin.
    cusp_trace := CuspDimension(Mk : version := "trace");
    delete Mk`CuspDimension;
    cusp_builtin := CuspDimension(Mk : version := "builtin");
    assert cusp_trace eq cusp_builtin;
    assert cusp_trace eq expected_cusp[k];

    delete Mk`CuspDimension;
    assert Dimension(Mk) eq expected_total[k];

    // Precision helper must return an integer consistent with dim M_k.
    prec := ComputePrecisionFromHilbertSeries(NN, k);
    assert Type(prec) eq RngIntElt;
    assert prec eq 10 * expected_total[k] + 10;
end for;
