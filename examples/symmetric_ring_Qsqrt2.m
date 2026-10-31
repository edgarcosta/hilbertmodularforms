// Hammond's ring is fixed by Hirzebruch's sign change on the weight-14
// generator, transported through the stored full-ring witness.
// Keep eval at top level: nested procedure eval crashes the runner.

H<t> := FunctionField(Rationals());
expected := 1/((1 - t^2)*(1 - t^4)*(1 - t^6));
J := LoadStoredCanonicalRing("2.2.8.1-1.1");
R := Generic(J);
assert VariableWeights(R) eq [2, 4, 6, 14];

litfile := "Verification/LiteratureEquations/2.2.8.1-1.1-Hirzebruch.m";
LitData := eval (Read(litfile) cat "return LitData;");
symfile := "Verification/LiteratureEquations/2.2.8.1-1.1-HammondSymmetric.m";
symmetric_lit_data := eval (Read(symfile) cat "return symmetric_lit_data;");

L, phi, psi, _ := LitData(R, R);
assert VerifyGradedIsomorphism(L, J, phi, psi);
litTau := [R.1, R.2, R.3, -R.4];
assert VerifyGradedIsomorphism(L, L, litTau, litTau);
tau := [Evaluate(Evaluate(f, litTau), phi) : f in psi];
assert VerifyGradedIsomorphism(J, J, tau, tau);

I, images, citation := symmetric_lit_data(R);
assert not IsEmpty(images);
assert &and[Evaluate(f, tau) - f in J : f in images];
K, _, hs := SymmetricSubringPresentation(J, tau);
assert VariableWeights(Generic(K)) eq [2, 4, 6];
assert K eq ideal<Generic(K) |>;
assert IsSymmetricSubringPresentation(J, tau, I, images);
assert H!hs eq expected and H!HilbertSeries(I) eq expected;

skew := phi[4];
assert skew notin J;
assert Evaluate(skew, tau) + skew in J;
assert tau[4] - R.4 notin J;
assert H!HilbertSeries(J) eq (1 + t^14)*expected;
printf "D=8: %o certified against the swap-fixed subring\n", citation;
