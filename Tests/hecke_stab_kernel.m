F := QuadraticField(5);
ZF := Integers(F);
prec := 13;
pp := 2*ZF;
M := GradedRingOfHMFs(F, prec);
triv_char := HeckeCharacterGroup(1*ZF, [1,2]).0;

N := 7*ZF; 
H := HeckeCharacterGroup(N, [1,2]);

chi := H.1^3;

M11chi := HMFSpace(M, N, [1,1], chi);
eis := EisensteinSeries(M11chi, chi, triv_char);

M_22 := HMFSpace(M, N, [2,2]);
M_44 := HMFSpace(M, N, [4,4]);

B_44 := CuspFormBasis(M_44);

B_22 := CuspFormBasis(M_22);

// The space of [2,2] forms of this level 
// is one-dimensional, spanned
// by a form whose coefficient corresponding
// to the ideal (2) is 0. Therefore, this form
// lies in the kernel of the action of Tpp on
// on V. 
V := [f/eis^2 : f in B_44];
W := HeckeStableSubspace(V, pp);
assert #LinearDependence(W cat B_22) eq #B_22;
