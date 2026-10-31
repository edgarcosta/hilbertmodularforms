// Hermann's abstract presentation is checked in the stored D=17 ring;
// the five normalized theta series are not identified.
// Keep eval at top level: nested procedure eval crashes the runner.

J := LoadStoredCanonicalRing("2.2.17.1-1.1");
R := Generic(J);
datafile := "Verification/LiteratureEquations/2.2.17.1-1.1-HermannSymmetric.m";
symmetric_lit_data := eval (Read(datafile) cat "return symmetric_lit_data;");
I, images, citation := symmetric_lit_data(R);

// The stored swap images came from q-expansions at precision 200;
// their derivation is not in the tree.
tau := [R.1, R.2, R.3, R.1*R.3 - R.4 + 4*R.5 + R.6, R.5, R.6,
  -R.2^2/4 - 3*R.2*R.3/2 + 15*R.3^2/4 + R.1*R.5 + R.1*R.6/4 - R.7];
assert VerifyGradedIsomorphism(J, J, tau, tau);
assert IsHomogeneous(I);
assert Sort([WeightedDegree(f) : f in Basis(I)]) eq [10, 12, 12];
assert IsSymmetricSubringPresentation(J, tau, I, images);
K, _, hs := SymmetricSubringPresentation(J, tau);
assert VariableWeights(Generic(K)) eq [2, 4, 4, 6, 6];
assert HilbertSeries(I) eq HilbertSeries(K);
H<t> := FunctionField(Rationals());
assert H!hs eq (1 - t^10 - 2*t^12 + t^16 + t^18)/((1 - t^2)*(1 - t^4)^2*(1 - t^6)^2);
printf "D=17: %o certified against the swap-fixed subring\n", citation;
