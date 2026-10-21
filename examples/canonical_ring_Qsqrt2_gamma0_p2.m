// Certify the even Gamma0(p2) invariants of van der Geer, Hilbert Modular Surfaces
// (1988), VIII.2.9, p.195, against the stored canonical ring over Q(sqrt2).
// Keep eval at top level: nesting it inside a procedure crashes the test runner.
SetNthreads(4);
J := LoadStoredCanonicalRing("2.2.8.1-2.1");
R := Generic(J);
assert VariableWeights(R) eq [2, 2, 4, 10];

litfile := "Verification/LiteratureEquations/2.2.8.1-2.1-vdGeer.m";
LitData := eval (Read(litfile) cat "\nreturn LitData;");
S := PolynomialRing(Rationals(), VariableWeights(R));
I, PhiImages, PsiImages, citation := LitData(S, R);

assert [WeightedDegree(f) : f in Basis(I)] eq [20];
HI := HilbertSeries(I);
HJ := HilbertSeries(J);
assert HI eq HJ;
P<q> := PowerSeriesRing(Rationals(), 41);
expected := (1+q^10)/((1-q^2)^2*(1-q^4));
assert [Coefficient(P!HI, k) : k in [0..40]] eq
  [Coefficient(expected, k) : k in [0..40]];

assert VerifyGradedIsomorphism(I, J, PhiImages, PsiImages);
bad := PhiImages;
bad[4] +:= R.1^5;
assert not VerifyGradedIsomorphism(I, J, bad, PsiImages);
printf "Q(sqrt2) Gamma0(p2): graded-isomorphic over Q to %o.\n", citation;
