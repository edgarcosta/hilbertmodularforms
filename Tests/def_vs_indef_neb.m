// Cross-check the DEFINITE method against the INDEFINITE method for a
// paritious space with nontrivial (quadratic) nebentypus.
//
// Idea (JL): over a real quadratic field, the indefinite method computes
// S_k(N, chi) by ramifying the quaternion algebra at a prime qq | N and
// one infinite place, with Eichler level N/qq; this yields exactly the
// qq-NEW subspace. In H^1 each newform appears with multiplicity 2, so the
// indefinite Hecke characteristic polynomial is a perfect square, and its
// square root (= the char poly on the qq-new subspace) must divide the
// characteristic polynomial of the Hecke operator on the full definite
// space S_k(N, chi). We check that divisibility at several good primes.
//
// For a quadratic (order 2) character the Hecke eigenvalues are rational,
// so everything lives in Q[x].

import "ModFrmHil/diamond.m" : HeckeCharacterSubspace;

F := QuadraticField(5);
ZF := Integers(F);
N := 6*ZF;
k := [3, 3];
H := HeckeCharacterGroup(N, [1, 2]);
chi := H.1;
assert Order(chi) eq 2;

// qq = prime over 2: exponent 1 in N, and N/qq = (3) = Conductor(chi),
// so chi still makes sense at the Eichler level N/qq.
qq := Factorization(2 * ZF)[1][1];
assert Valuation(N, qq) eq 1;
assert (N / qq) subset Conductor(chi);

// --- DEFINITE: full space S_k(N, chi) ---
Mdef := HilbertCuspForms(F, N, chi, k);
Sdef := HeckeCharacterSubspace(Mdef, chi);
assert IsDefinite(Mdef);
assert Dimension(Sdef) eq 4;

// --- INDEFINITE: ramify at qq, Eichler level N/qq, chi restricted ---
B := QuaternionAlgebra(qq, [InfinitePlaces(F)[1]]);
O := MaximalOrder(B);
Gamma := FuchsianGroup(O);
_, K := Splittings(B);
Nind := N / qq;
chi_ind := Restrict(chi, Nind, [1, 2]);

QX := PolynomialRing(Rationals());
checked := 0;
for pp in PrimesUpTo(23, F) do
  if Norm(N + pp) ne 1 then
    continue;   // good primes only (coprime to the level)
  end if;
  cd := QX ! CharacteristicPolynomial(HeckeOperator(Sdef, pp));
  Ti := HeckeMatrix2(Gamma, Nind, pp, k, chi_ind : HeckeMatrixField := K);
  ci := QX ! CharacteristicPolynomial(Ti);

  // indefinite char poly is a perfect square; its root divides the definite one
  issq, sq := IsSquare(ci);
  assert issq;
  assert IsDivisibleBy(cd, sq);
  checked +:= 1;
end for;
assert checked ge 3;
