/***************************************************
 * There is exactly one [1,1] dihedral form of level N.
 * We check that it's in the cusp space (computed via
 * Hecke stability). We then check that the forms
 * are included into the dihedral space of level 2*N.
***************************************************/

F := QuadraticField(5);
ZF := Integers(F);
N := ideal<ZF | 241, 2*ZF.2 + 137>;
M := GradedRingOfHMFs(F, 150);
H := HeckeCharacterGroup(N, [1,2]);
chi := H.1^11; // (H.1^11); // aka 11 mod 22
G := HeckeCharacterGroup(2*N, [1,2]);
psi := Extend(chi, G);
assert chi eq Restrict(psi, H);

Mk1 := HMFSpace(M, N, [1,1], chi);
Sk1 := HeckeStabilityCuspBasis(Mk1 : prove:=false);
Dk1 := DihedralBasis(Mk1);

// there should be one dihedral form of this level
assert #Dk1 eq 1;
// Dk1 should be linearly independent
assert #LinearDependence(Dk1) eq 0;
// Dk1 should be contained in Sk1
assert #LinearDependence(Sk1 cat Dk1) eq #Dk1;

Mk2 := HMFSpace(M, 2*N, [1,1], psi);
Sk2 := HeckeStabilityCuspBasis(Mk2 : prove:=false, stable_only:=true);
Dk2_old := OldDihedralBasis(Mk2);

// Dk2_old should be linearly independent
assert #LinearDependence(Dk2_old) eq 0;
// Dk2_old should be contained in Sk2
assert #LinearDependence(Sk2 cat Dk2_old) eq #Dk2_old;
// the size of Dk1 should be the twice that of Dk2_old
assert #Dk2_old eq 2 * #Dk1;

/***************************************************
 * We verify that the Moy-Specter form is not dihedral
***************************************************/

F := QuadraticField(5);
ZF := Integers(F);
prec := 550;
M := GradedRingOfHMFs(F, prec);
N := 14*ZF;
H := HeckeCharacterGroup(N, [1,2]);
H_prim := HeckeCharacterGroup(7*ZF, [1,2]);
chi_prim := (H_prim).1;
chi := H.1;
M15chi := HMFSpace(M, N, [1,5], chi);
D15chi := DihedralBasis(M15chi);
assert #D15chi eq 0;
