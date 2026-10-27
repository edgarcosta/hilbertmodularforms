// Exact domain certificates for graded presentations over Q.
SetNthreads(1);
SetSeed(1);
Q := Rationals();
R<x,y,z,w> := PolynomialRing(Q, 4);
I := ideal<R | w^2 - 2*x^2>;
proved, proof := CertifyGradedDomain(I);
assert proved and proof`Method eq "hypersurface factorization";
assert proof`Status eq "domain proved";
assert #proof`Steps eq 1;

R<a,b,c,d,e> := PolynomialRing(Q, 5);
I := ideal<R | a*b-c^2, d*e-a^2>;
proved, proof := CertifyGradedDomain(I);
assert proved and proof`Method eq "complete intersection normality";
assert proof`Steps[2][3] le 1;

R<a,b,c,d,e,f> := PolynomialRing(Q, 6);
I := ideal<R | b^2-a*d, b*c-a*e, b*e-c*d,
                  c^2-a*f, c*e-b*f, e^2-d*f>;
proved, proof := CertifyGradedDomain(I : Parameters := [a,d,f]);
assert proved and proof`Method eq "Cohen-Macaulay specialization";
assert #proof`Point eq 3;
assert proof`Parameters eq [a,d,f];
assert IsIrreducible(proof`CharacteristicPolynomial);

proved, proof := CertifyGradedDomain(I);
assert proved and proof`Method eq "Cohen-Macaulay specialization";
assert #proof`Parameters eq 3;

R<x,y,z,u,v> := PolynomialRing(Q, [2,3,2,3,1]);
I := ideal<R | y^2-x^3, u^2-z^3>;
proved, proof := CertifyGradedDomain(I : ParameterAttempts := 0, PrimeTimeLimit := 10);
assert proved and proof`Method eq "IsPrime";
proved, proof := CertifyGradedDomain(I : ParameterAttempts := 0, PrimeTimeLimit := 0);
assert not proved and proof`Status eq "domain unproved";
assert proof`Steps[#proof`Steps][2] eq "budget exhausted";

// The fallback must return after its child is interrupted.
R<x,y,z,u,v> := PolynomialRing(Q, [101,103,107,109,1]);
I := ideal<R | y^101-x^103, u^107-z^109>;
proved, proof := CertifyGradedDomain(I : ParameterAttempts := 0, PrimeTimeLimit := 1);
assert not proved and proof`Status eq "domain unproved";
assert proof`Steps[#proof`Steps][2] eq "no result within budget";

R<x,y,z,w> := PolynomialRing(Q, 4);
I := ideal<R | x*y>;
assert HilbertSeries(I) eq HilbertSeries(ideal<R | x*y-z*w>);
proved, proof := CertifyGradedDomain(I);
assert not proved and proof`Status eq "not a domain";
proved, proof := CertifyGradedDomain(ideal<R | x^2>);
assert not proved and proof`Status eq "not a domain";

R<x,y,z,w,v> := PolynomialRing(Q, 5);
I := ideal<R | x*y, z^2+w^2+v^2>;
assert Dimension(I) eq 3;
assert x notin I and y notin I and x*y in I;
proved, proof := CertifyGradedDomain(I);
assert not proved and proof`Status ne "domain proved";

I := ideal<R | x^2, x*y+y^2+z^2+w^2+v^2>;
assert Dimension(I) eq 3;
assert x notin I and x^2 in I;
proved, proof := CertifyGradedDomain(I);
assert not proved and proof`Status ne "domain proved";
printf "Domain cascade: PASSED\n";
