// The literature loader certifies generation and all relations of Williams' even subring.
// Keep eval at top level: nesting it inside a procedure crashes the test runner.
SetNthreads(8);
t0 := Cputime();
J := LoadStoredCanonicalRing("2.2.37.1-1.1");
R := Generic(J);
assert VariableWeights(R) eq [2, 2, 4, 4, 6, 6, 6, 6, 6, 8, 8];

litfile := "Verification/LiteratureEquations/2.2.37.1-1.1-Williams.m";
LitData := eval (Read(litfile) cat "\nreturn LitData;");
// Matching monomial-order weights to the grading keeps the Hilbert check small.
S := PolynomialRing(Rationals(), VariableWeights(R));
I, PhiImages, PsiImages, citation := LitData(S, R);
HI := HilbertSeries(I);
HJ := HilbertSeries(J);
assert HI eq HJ;
P := PowerSeriesRing(Rationals(), 41);
HI41 := P!HI;
HJ41 := P!HJ;
assert [Coefficient(HI41, w) : w in [0..40]] eq
  [Coefficient(HJ41, w) : w in [0..40]];

// Hilbert computations expand the generator lists to Groebner bases.
// Restore minimal generators before substituting them in the witness maps.
I := ideal<Generic(I) | MinimalBasis(I)>;
J := ideal<Generic(J) | MinimalBasis(J)>;
assert VerifyGradedIsomorphism(I, J, PhiImages, PsiImages);
printf "Q(sqrt37) level 1: graded-isomorphic over Q to the even subring of %o. [%o s]\n",
  citation, Cputime(t0);
