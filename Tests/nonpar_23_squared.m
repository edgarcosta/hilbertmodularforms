// Testing computation of HMFs with nontrivial (quadratic) nebentypus
// using the definite method, in nonparitious weight [2,3].
//
// Computes a weight [2,3] cusp form space with quadratic nebentypus at
// the lowest level where it is nonzero, and checks that squaring it
// lands inside the (trivial-character) weight [4,6] cusp forms.
//
// This is a fixed, working version of the old (disabled) _23_squared.m:
// that file referenced an undefined variable (chi_12) and never actually
// asserted its computed booleans, so it always vacuously "passed" without
// checking anything. It's also genuinely slow (the weight [4,6] space at
// this level has dimension 90), so budget several minutes for this test.

F := QuadraticField(2);
ZF := Integers(F);

M := GradedRingOfHMFs(F, 500);
N := ideal<ZF | 119, -ZF.2 - 45>;

H := HeckeCharacterGroup(N, [1, 2]);
chi := H.2;
assert Order(chi) eq 2;

Mk := HMFSpace(M, N, [2, 3], chi);
Sk := CuspFormBasis(Mk);
assert #Sk eq 12;
assert #LinearDependence(Sk) eq 0;

M46 := HMFSpace(M, N, [4, 6]);
S46 := CuspFormBasis(M46);
assert #S46 eq 90;
assert #LinearDependence(S46) eq 0;

f := Sk[1];
assert #Intersection([f^2], S46) eq 1;
