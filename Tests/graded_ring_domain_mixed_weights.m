SetNthreads(1);
SetSeed(1);
I := eval (Read("Verification/CanonicalRingEquations/2.2.5.1-31.2-gl-0.m")
    cat "return ideal<R | eqns>;");
proved, proof := CertifyGradedDomain(I : PrimeTimeLimit := 0);
printf "Mixed-weight domain: %o (%o)\n", proof`Status, proof`Method;
assert proved and proof`Status eq "domain proved";
assert proof`Method eq "Cohen-Macaulay specialization";
assert proof`Ideal eq I;
assert IsIrreducible(proof`CharacteristicPolynomial);
printf "Mixed-weight domain: PASSED\n";
