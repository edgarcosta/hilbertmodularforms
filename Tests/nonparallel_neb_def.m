F := QuadraticField(5);
ZF := Integers(F);
M := GradedRingOfHMFs(F, 444);

k := [2, 4];

N := ideal<ZF | 29, 2*ZF.2 + 10>;
H := HeckeCharacterGroup(N, [1,2]);
chi := H.1^2;
assert HeckeCharLabel(chi) eq "-5.0.1_29.1_2u1u1.2u";
M24chi := HMFSpace(M, N, k, chi);
S24chi := CuspFormBasis(M24chi);

M48 := HMFSpace(M, N, [4, 8]);
S48 := CuspFormBasis(M48);

assert #LinearDependence(S24chi) eq 0;
assert #LinearDependence(S48) eq 0;

assert #S24chi eq 2;
// TODO abhijitm uncomment once you fix the dihedral basis code
// assert #Intersection(S24chi, DihedralBasis(M24chi)) eq 2;
f := S24chi[1];
g := S24chi[2];
assert #Intersection([f^2, f*g, g^2], S48) eq 3;
