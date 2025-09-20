F := QuadraticField(2);
K := CyclotomicField(8);
ZK := Integers(K);
_ := IsSubfield(F, K);

N := Factorization(41*ZK)[1][1];
D := DirichletGroup(N);

F_units := UnitsGenerators(F);
zeta := K.1;

auts := AutsOfKReppingEmbeddingsOfF(F, K);

F_vs := InfinitePlaces(F);
sign_1 := func<x | Sign(Evaluate(x, F_vs[1]))>;

flag := false;
for psi in Elements(D) do
  if (psi(zeta)^-1 eq (auts[2](K.1))) and &and[psi(K!u)^-1 eq (u * auts[2](u) * sign_1(u)) : u in F_units] then
    psi_D := psi;
    if not flag then
      flag := true;
    else
      // there should be only one such psi
      assert 0 eq 1;
    end if;
  end if;
end for;

k_hmf := [1, 2];
k := HeckeCharWeightFromWeight(K, F, k_hmf);
print k;
X := cHMFGrossencharsTorsor(K, k, N);
S := HMFGrossencharsTorsorSet(X);
assert #S eq 1;
assert X`MarkedDrchChar eq psi_D^-1;
psi := Rep(S);
// f := ThetaSeries(Mk, psi);

// TODO abhijitm Magma has some weird issues with 
// this IsSubfield call, as it makes subsequent calls to
// compositum fail. i submitted this bug to Magma, but be aware for now.
_ := IsSubfield(F, K);
K_rel := RelativeField(F, K);
ZK_rel := Integers(K_rel);
N_F := Norm(ZK_rel!!N) * Discriminant(ZK_rel);
H := HeckeCharacterGroup(N_F, [1, 2]);

chi := H.1^7;
assert HeckeCharLabel(chi) eq "-2.0.1_164.1_8u7.2u1.2u";

M := GradedRingOfHMFs(F, 200);
// Mk := HMFSpace(M, N, k_hmf, chi);
// Dk := DihedralBasis(Mk);
// assert #Dk eq 1;
// assert #LinearDependence([f, Dk[1]]) eq 1;

