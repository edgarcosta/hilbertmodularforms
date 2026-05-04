// TODO: re-enable once Magma-Maths/Magma#55 is fixed.
// The Embed at package/RepThry/ModGrp/Reduce-NonCyclic.m:231 (intrinsic
// Compositum(FldAlg, FldAlg), line 132) fails with
//   "Runtime error in 'Embed': Invalid embedding"
// once Compositum has been called with a (FldQuad, FldCyc) pair in
// both argument orders. Reached via ModFrmHilD/Space.m:613
// (DefaultCoefficientRing) when constructing a non-parallel-weight +
// non-trivial-nebentypus HMFSpace.
// Regression bracket: works on V2.28-25; crashes on V2.29-beta0
// through V2.29-7.
/****************************************************************
* Finds a weight [3,1] CM form of level a prime above 41.
* TODO abhijitm add a check to match this with the 
* class field theory computation.
****************************************************************/

F := QuadraticField(5);
prec := 200;
ZF := Integers(F);
M := GradedRingOfHMFs(F, prec);
N := Factorization(41*ZF)[1][1];
H := HeckeCharacterGroup(N, [1,2]);
chi := H.1;
M13chi := HMFSpace(M, N, [3,1], chi);
B13chi := HeckeStabilityCuspBasis(M13chi);

assert #B13chi eq 1;

/****************************************************************
* Finds a weight [3,1] form of level 14 and order 6 nebentypus.
* Because the nebentypus is not quadratic, this form is not CM.
* This reproduces the example constructed by Moy and Specter in
* https://arxiv.org/abs/1407.3872
*
* TODO abhijitm implement the holomorphicity checking step.
* For now we just find a 2-dimensional Hecke-stable subspace
****************************************************************/

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

M26 := HMFSpace(M, N, [2,6]);
B26 := CuspFormBasis(M26);

MEis := HMFSpace(M, N, [1,1], chi^-1);

triv_char := HeckeCharacterGroup(1*ZF, [1, 2]).0;
E := EisensteinSeries(MEis, chi_prim^-1, triv_char);
V := [f/E : f in B26];

pp := 3*ZF;
U := HeckeStableSubspace(V, pp);
assert #U eq 2;
