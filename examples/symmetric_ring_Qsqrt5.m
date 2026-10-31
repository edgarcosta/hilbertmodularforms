// Gundlach and Hammond's ring is fixed by Hirzebruch's sign change on the
// weight-20 generator, transported through the stored full-ring witness.
// Keep eval at top level: nested procedure eval crashes the runner.

H<t> := FunctionField(Rationals());
expected := 1/((1 - t^2)*(1 - t^6)*(1 - t^10));
J := LoadStoredCanonicalRing("2.2.5.1-1.1");
R := Generic(J);
assert VariableWeights(R) eq [2, 6, 10, 20];

litfile := "Verification/LiteratureEquations/2.2.5.1-1.1-Hirzebruch.m";
LitData := eval (Read(litfile) cat "return LitData;");
symfile := "Verification/LiteratureEquations/2.2.5.1-1.1-GundlachHammondSymmetric.m";
symmetric_lit_data := eval (Read(symfile) cat "return symmetric_lit_data;");

L, phi, psi, _ := LitData(R, R);
assert VerifyGradedIsomorphism(L, J, phi, psi);
litTau := [R.1, R.2, R.3, -R.4];
assert VerifyGradedIsomorphism(L, L, litTau, litTau);
tau := [Evaluate(Evaluate(f, litTau), phi) : f in psi];
assert VerifyGradedIsomorphism(J, J, tau, tau);
assert tau eq [R.1, R.2, R.3, R.1*R.2^3/4 - R.1^2*R.2*R.3/4 + 13*R.3^2 - R.4];

I, images, citation := symmetric_lit_data(R);
assert not IsEmpty(images);
assert &and[Evaluate(f, tau) - f in J : f in images];
K, _, hs := SymmetricSubringPresentation(J, tau);
assert VariableWeights(Generic(K)) eq [2, 6, 10];
assert K eq ideal<Generic(K) |>;
assert IsSymmetricSubringPresentation(J, tau, I, images);
assert H!hs eq expected and H!HilbertSeries(I) eq expected;

skew := phi[4];
assert skew notin J;
assert Evaluate(skew, tau) + skew in J;
assert tau[4] - R.4 notin J;
assert H!HilbertSeries(J) eq (1 + t^20)*expected;
printf "D=5: %o certified against the swap-fixed subring\n", citation;
