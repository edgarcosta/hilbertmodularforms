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
