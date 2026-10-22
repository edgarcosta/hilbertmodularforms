// van der Geer and Zagier, Invent. Math. 42 (1977), Theorem 7, p.119.
// Symmetric even forms on SL2(O_Q(sqrt13)), with actual parallel weights.
// The p.130 convention f(z1,z2)=(-1)^k*f(z2,z1) is geometric swap in even weight.
// The example composes the full-ring witness's first four images into the stored ring.

SymmetricLitData := function()
    P<A,B,C,Cprime> := PolynomialRing(Rationals(),[2,4,6,6]);
    I := ideal<P | B^3-C*Cprime>;
    citation := "van der Geer and Zagier, Invent. Math. 42 (1977), Theorem 7, p.119";
    return I,citation;
end function;
return SymmetricLitData;
