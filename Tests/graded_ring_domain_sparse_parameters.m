SetNthreads(1);
SetSeed(1);
I := eval (Read("Tests/data/graded_domain_d40.m") cat "return ideal<R | eqns>;");
Alarm(20);
proved, proof := CertifyGradedDomain(I);
Alarm(0);
assert proved and proof`Status eq "domain proved";
assert proof`Method eq "Cohen-Macaulay specialization";
assert proof`Ideal eq I;
assert IsIrreducible(proof`CharacteristicPolynomial);
printf "Stored sparse parameters: PASSED\n";

// Four coordinate axes lie on this scroll, so no three generators are parameters.
R<a,b,c,d,e,f> := PolynomialRing(Rationals(), 6);
I := ideal<R | a*c-b^2, a*e-b*d, a*f-b*e, b*e-c*d, b*f-c*e, d*f-e^2>;
SetSeed(1);
proved, proof := CertifyGradedDomain(I : PrimeTimeLimit := 0);
assert proved and proof`Method eq "Cohen-Macaulay specialization";
assert Dimension(I + ideal<R | proof`Parameters>) eq 0;
assert exists{g : g in proof`Parameters | #Terms(g) gt 1};
printf "Sparse sums: PASSED\n";
