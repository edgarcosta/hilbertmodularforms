// Gundlach, Math. Ann. 152 (1963), Satz 5-6, p.241: the abstract rational
// presentation of the symmetric even ring for SL2(O_Q(sqrt5)).
// The stored map does not identify his G_{-2}, G_{-6}, or Theta^2.
SetNthreads(4);
H<t> := FunctionField(Rationals());
expected := 1/((1-t^2)*(1-t^6)*(1-t^10));
J := LoadStoredCanonicalRing("2.2.5.1-1.1");
R := Generic(J);
assert VariableWeights(R) eq [2,6,10,20];

// Keep eval at top level: nested procedure eval crashes the test runner.
SymmetricLitData := eval Read("Verification/LiteratureEquations/2.2.5.1-1.1-GundlachSymmetric.m");
I, citation, storedImages := SymmetricLitData();
P := Generic(I);
assert VariableWeights(P) eq [2,6,10];
assert I eq ideal<P | >;
assert VariableWeights(Universe(storedImages)) eq VariableWeights(R);
storedImages := [R | f : f in storedImages];
assert #storedImages eq 3;
assert &and[IsHomogeneous(storedImages[i]) and
    WeightedDegree(storedImages[i]) eq VariableWeights(P)[i] : i in [1..3]];

LitData := eval Read("Verification/LiteratureEquations/2.2.5.1-1.1-Hirzebruch.m");
L, phi, psi, fullCitation := LitData(R,R);
assert VerifyGradedIsomorphism(L,J,phi,psi);
litTau := [R.1,R.2,R.3,-R.4];
tau := [Evaluate(Evaluate(f,litTau),phi) : f in psi];
assert VerifyGradedIsomorphism(J,J,tau,tau);
assert tau eq [R.1,R.2,R.3,
    R.1*R.2^3/4-R.1^2*R.2*R.3/4+13*R.3^2-R.4];
assert &and[Evaluate(f,tau)-f in J : f in storedImages];

K, inclusion, hs := SymmetricSubringPresentation(J,tau);
Q := Generic(K);
assert VariableWeights(Q) eq [2,6,10];
assert K eq ideal<Q | >;
assert VerifySymmetricSubringPresentation(J,tau,K,inclusion);
sourceToFixed := [Q.i : i in [1..3]];
fixedToSource := [P.i : i in [1..3]];
assert VerifyGradedIsomorphism(I,K,sourceToFixed,fixedToSource);
composed := [Evaluate(f,inclusion) : f in sourceToFixed];
assert &and[composed[i]-storedImages[i] in J : i in [1..3]];
// This verifier checks the exact graph kernel and generation of all invariants.
assert VerifySymmetricSubringPresentation(J,tau,I,storedImages);
assert H!hs eq expected and H!HilbertSeries(I) eq expected;
assert H!HilbertSeries(K) eq expected;

skew := phi[4];
assert skew notin J;
assert Evaluate(skew,tau)+skew in J;
assert Evaluate(skew,tau)-skew notin J;
assert H!HilbertSeries(J) eq (1+t^20)*expected;
printf "SOURCE %o\nINCLUSION %o\nKERNEL %o\n",citation,storedImages,Basis(I);
printf "SERIES %o\nEXCLUDED nonzero skew form of weight %o\n",expected,WeightedDegree(skew);
print "PASS Gundlach D5 symmetric";
