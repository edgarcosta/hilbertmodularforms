/**************************************************
* Test for finite-order characters
* Note that because of the torsor implementation,
* if psith is a ray class character, the psi-th element 
* of the torsor may not be psi. 
**************************************************/
procedure test_finite_order(K, k, N)
  // K - a number field
  // k - a weight
  // N - a finite conductor
  X := cHMFGrossencharsTorsor(K, k, N);
  S := HMFGrossencharsTorsorSet(X);
  
  assert IsNonempty(X);
  assert assigned X`MarkedDrchChar;

  r, s := Signature(K);
  G, mp := RayClassGroup(N, [1 .. r]);
  reps := [mp(G.i) : i in [1 .. #Generators(G)]];
  
  MIN_COUNT := 4;
  H := HeckeCharacterGroup(N, [1 .. r]);
  // the order of S should be that of the corresponding ray class group
  assert #H eq #S;

  trials := Min(MIN_COUNT, #H);

  for _ in [1 .. trials] do
    psi := Random(H);
    flag := false;
    for chi in S do
      if &and[chi(rep) cmpeq psi(rep) : rep in reps] then
        if flag eq false then
          flag := true;
        else
          // there should be only one chi in S which agrees with psi
          assert 0 eq 1;
        end if;
        // Conductors should be the same
        assert Conductor(chi) eq Conductor(psi);
      end if;
    end for;
    // There should be some chi in the torsor
    // agreeing with psi
    assert flag;
  end for;
end procedure;

// n = 2, h = 1, totally real, finite order
K := QuadraticField(5);
ZK := Integers(K);
k := [<0,0>, <0,0>];
N := 48*ZK;
test_finite_order(K, k, N);

N := Factorization(41*ZK)[2][1];
test_finite_order(K, k, N);

// n = 2, h = 4, totally real, finite order
K := QuadraticField(39);
ZK := Integers(K);
k := [<0,0>, <0,0>];
N := 23*ZK;
test_finite_order(K, k, N);

// n = 4, h = 1, totally imaginary, finite order
K := CyclotomicField(8);
ZK := Integers(K);
k := [<0,0>, <0,0>];
N := 11*ZK;
test_finite_order(K, k, N);

// n = 3, h = 1, finite order
R<x> := PolynomialRing(Rationals());
K := NumberField(x^3 - x^2 - 2*x + 1);
ZK := Integers(K);
k := [<0,0>, <0,0>, <0,0>];
N := 7*ZK;
test_finite_order(K, k, N);

// n = 3, h = 1, non-Galois, mixed signature, finite order
K := NumberField(x^3 - 2);
ZK := Integers(K);
k := [<0,0>, <0,0>, <0,0>];
N := Factorization(5*ZK)[1][1];

/**************************************************
* Test computation of associated primitive character
**************************************************/

F := QuadraticField(5);
M := 108*Integers(F);
H := HeckeCharacterGroup(M, [1,2]);
psi := H.1;
assert not IsPrimitive(psi);
psi_prim := AssociatedPrimitiveCharacter(psi);
N_psi_f, N_psi_oo := Conductor(psi);

X := cHMFGrossencharsTorsor(F, [<0,0>, <0,0>], M : N_oo:=[1,2]);
reps := RayClassGroupReps(X);
S := HMFGrossencharsTorsorSet(X);
for eta in S do
  if eta`RayClassChar eq psi then
    chi := eta;
    break;
  end if;
end for;

assert [* chi(rep) : rep in reps *] cmpeq [* psi(rep) : rep in reps *];
chi_prim := AssociatedPrimitiveCharacter(chi);
N_chi_f, N_chi_oo := Conductor(chi);
assert N_chi_f eq N_psi_f;
assert N_chi_oo eq N_psi_oo;

G, mp := RayClassGroup(N_psi_f, N_psi_oo);
new_reps := [mp(gen) : gen in Generators(G)];
assert [chi_prim(rep) : rep in new_reps] cmpeq [psi(rep) : rep in new_reps];
