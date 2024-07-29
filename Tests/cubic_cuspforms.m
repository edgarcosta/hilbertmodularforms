// Checks that the restrictions of parallel weight cusp forms over
// cubic fields are classical cusp forms. 
//
// TODO abhijitm - this test will be made more robust shortly, once we can compute
// parallel weight k forms for k > 2. 

R<x> := PolynomialRing(Rationals());
F := NumberField(x^3-x^2-2*x+1);
ZF := Integers(F);

M := GradedRingOfHMFs(F, 150);
N := 3*ZF;
M222 := HMFSpace(M, N, [2,2,2]);
S222 := CuspFormBasis(M222);
assert #S222 eq 1;
f := S222[1];

// The restriction of a parallel weight 2 form f to the diagonal g(z) := f(z,z,z)
// should be a weight 6 classical modular form of level 3:
g := RestrictionToDiagonal(f, M, 1*ZF);

// the space of level 3 weight 6 forms has dimension 1
// https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/3/6/a/a/
h := Basis(CuspForms(Gamma0(3), 6))[1];

assert Degree(F) * h eq g;
