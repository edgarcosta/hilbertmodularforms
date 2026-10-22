// Cross-check the DEFINITE and INDEFINITE methods on a nonparitious weight
// [2,3] space with quadratic nebentypus (the upstairs space used by weight-1
// Hecke stability). As in def_vs_indef_neb.m (paritious case), the indefinite
// method ramifies at a prime qq | N with Eichler level N/qq and computes the
// qq-new subspace, in which each form appears with multiplicity 2; so its Hecke
// char poly is a perfect square whose eigenvalues occur among those of the full
// definite space. Here N/qq = Conductor(chi) and there are no qq-oldforms, so
// the qq-new subspace is the whole space and the eigenvalue sets coincide.
//
// Exact coercion between the two methods' coefficient fields is fragile for
// nonparitious weight, so we compare the eigenvalues numerically.

import "ModFrmHil/diamond.m" : HeckeCharacterSubspace;

F := QuadraticField(2);
ZF := Integers(F);
N := ideal<ZF | 119, -ZF.2 - 45>;
k := [2, 3];
H := HeckeCharacterGroup(N, [1, 2]);
chi := H.2;
assert Order(chi) eq 2;

// --- DEFINITE: full space S_[2,3](N, chi) ---
Mdef := HilbertCuspForms(F, N, chi, k);
Sdef := HeckeCharacterSubspace(Mdef, chi);
assert IsDefinite(Mdef);
assert Dimension(Sdef) eq 12;

// --- INDEFINITE: ramify at qq | N, Eichler level N/qq, chi restricted ---
qq := [t[1] : t in Factorization(N) | t[2] eq 1 and (N / t[1]) subset Conductor(chi)][1];
Nind := N / qq;
B := QuaternionAlgebra(qq, [InfinitePlaces(F)[1]]);
Gamma := FuchsianGroup(MaximalOrder(B));
_, K := Splittings(B);
chi_ind := Restrict(chi, Nind, [1, 2]);

// numeric roots of a char poly over a number field (one complex embedding of each coeff)
numroots := func< f | [ComplexField(10) ! r[1] :
  r in Roots(Polynomial([Conjugates(c : Precision:=30)[1] : c in Coefficients(f)]))] >;

// multiset equality within tolerance (greedy matching with multiplicity)
function same_multiset(A, B)
  if #A ne #B then return false; end if;
  used := [false : _ in B];
  for a in A do
    matched := false;
    for j in [1..#B] do
      if not used[j] and Abs(a - B[j]) lt 1e-6 then
        used[j] := true; matched := true; break;
      end if;
    end for;
    if not matched then return false; end if;
  end for;
  return true;
end function;

checked := 0;
for pp in PrimesUpTo(40, F) do
  if Norm(N + pp) ne 1 then
    continue;   // good primes only
  end if;
  cd := CharacteristicPolynomial(HeckeOperator(Sdef, pp));
  ci := CharacteristicPolynomial(HeckeMatrix2(Gamma, Nind, pp, k, chi_ind : HeckeMatrixField := K));
  issq, sq := IsSquare(ci);
  assert issq;                          // multiplicity 2 in H^1
  // no oldforms here, so the qq-new eigenvalues equal the full-space ones
  assert same_multiset(numroots(cd), numroots(sq));
  checked +:= 1;
  if checked ge 3 then break; end if;
end for;
assert checked ge 3;
