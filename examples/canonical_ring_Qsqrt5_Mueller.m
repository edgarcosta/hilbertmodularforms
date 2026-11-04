// Certify the even-weight ring over Q(sqrt5) at level (1) against Mueller's
// Satz 1, Arch. Math. 45 (1985), using the equations and witness maps in LitData.
// Keep eval-loading at top level: nesting it in a procedure crashes the runner.
SetNthreads(4);
J := LoadStoredCanonicalRing("2.2.5.1-1.1");
R := Generic(J);
assert VariableWeights(R) eq [2, 6, 10, 20];

litfile := "Verification/LiteratureEquations/2.2.5.1-1.1-Mueller.m";
LitData := eval (Read(litfile) cat "\nreturn LitData;");
I, PhiImages, PsiImages, citation := LitData(R, R);

assert #Generators(I) eq 1;
assert IsHomogeneous(I);
assert WeightedDegree(Generators(I)[1]) eq 40;
assert HilbertSeries(I) eq HilbertSeries(J);
assert VerifyGradedIsomorphism(I, J, PhiImages, PsiImages);
printf "Q(sqrt5) level 1: VerifyGradedIsomorphism = true for %o.\n", citation;
