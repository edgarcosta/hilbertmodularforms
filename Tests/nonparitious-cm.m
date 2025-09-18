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
    psi_112 := psi;
    if not flag then
      flag := true;
    else
      // there should be only one such psi
      assert 0 eq 1;
    end if;
  end if;
end for;

k := HeckeCharWeightFromWeight(K, F, [1, 2]);
X := cHMFGrossencharsTorsor(K, k, N);
S := HMFGrossencharsTorsorSet(X);
assert #S eq 1;
assert X`MarkedDrchChar eq psi_112^-1;
