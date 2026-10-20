// code for testing Hecke stability and computation of spaces with 
// nontrivial nebentypus using the definite method

F := QuadraticField(2);
ZF := Integers(F);

M := GradedRingOfHMFs(F, 600);
N := ideal<ZF | 119, -ZF.2 - 45>;

H := HeckeCharacterGroup(N, [1, 2]);
chi := H.1;
assert HeckeCharLabel(chi) eq "-2.0.1_119.2_2u1.0u1.2u";

Mk := HMFSpace(M, N, [1, 2], chi);
Sk := CuspFormBasis(Mk : StableOnly:=true);
assert #Sk eq 2;

M24 := HMFSpace(M, N, [2,4]);
S24 := CuspFormBasis(M24);
assert #LinearDependence(S24) eq 0;

// TODO abhijitm add a check for them both passing probabilistic
// dihedrality test
// TODO abhijitm someday when the dihedral basis code works you should verify
// that the spaces are the same. 

f := Sk[1];
g := Sk[2];
assert #Intersection([f^2, f * g, g^2], S24) eq 3;
