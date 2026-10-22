// Weight-(1,2) Hecke stability with quadratic nebentypus (definite method):
// check that the Hecke-stable space is the expected CM space.
//
// At this level the space is 2-dimensional and both forms are CM (dihedral),
// induced from grossencharacters. We check that the Hecke-stable dimension
// equals the number of candidate grossencharacters, and that each eigenform
// passes the dihedrality test. (Squaring into weight (2,4) is checked in
// 12-form.m.)

F := QuadraticField(2);
ZF := Integers(F);
M := GradedRingOfHMFs(F, 150);
N := ideal<ZF | 119, -ZF.2 - 45>;
H := HeckeCharacterGroup(N, [1, 2]);
chi := H.1;

Mk := HMFSpace(M, N, [1, 2], chi);
Sk := CuspFormBasis(Mk : StableOnly:=true, Prove:=false);
assert #Sk eq 2;

// the Hecke-stable dimension matches the predicted number of CM forms
assert #PossibleGrossenchars(Mk) eq #Sk;

// each eigenform is dihedral (CM)
eigs := Eigenbasis(Mk, Sk);
assert &and[ProbabilisticDihedralTest(f) : f in eigs];
