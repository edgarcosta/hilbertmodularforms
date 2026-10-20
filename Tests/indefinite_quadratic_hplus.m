// test-time: ~20s
//
// Indefinite algorithm (ModFrmHil/level.m) over a real quadratic field with
// narrow class number > 1 and a nontrivial quaternion-order discriminant.
//
// Over an even-degree field the default backend is definite, and an indefinite
// quaternion algebra must ramify at an odd number of finite primes (one, here),
// so this simultaneously exercises: the indefinite method, narrow class number
// h+ > 1, and nontrivial order discriminant. The definite backend is the oracle:
// dimensions and Hecke characteristic polynomials must agree.
//
// This is a regression guard for the h+ > 1 fixes in level.m (robust H^1 lift
// via the quotient map, and an in-order element of norm -1 for the plus
// involution); before those, the indefinite path asserted nondeterministically
// for h+ > 1 at field-valued weight.

SetSeed(1);

R<x> := PolynomialRing(Rationals());
F := NumberField(x^2 - 10);
ZF := Integers(F);
assert NarrowClassNumber(F) eq 2;

// indefinite quaternion order: ramified at one infinite place and the prime pp
pp := Factorization(3*ZF)[1][1];
assert Norm(pp) eq 3;
Oind := MaximalOrder(QuaternionAlgebra(pp, [InfinitePlaces(F)[2]]));
assert not IsDefinite(Algebra(Oind));
assert Norm(Discriminant(Oind)) eq 3;

// primes coprime to the level, for Hecke comparison
Ps := [P : P in PrimesUpTo(20, F) | Norm(P + pp) eq 1];

expected_dims := AssociativeArray();
expected_dims[[2,2]] := 0;
expected_dims[[4,4]] := 18;
expected_dims[[2,4]] := 10;

for k in [[2,2], [4,4], [2,4]] do
  M := HilbertCuspForms(F, pp, k);

  // forced indefinite (goes through level.m::HeckeMatrix2)
  Sind := NewSubspace(M : QuaternionOrder := Oind);
  // default definite backend (oracle)
  Sdef := NewSubspace(M);

  dind := Dimension(Sind);
  ddef := Dimension(Sdef);
  assert dind eq ddef;
  assert dind eq expected_dims[k];

  cpind := [CharacteristicPolynomial(HeckeOperator(Sind, P)) : P in Ps[1..Min(3, #Ps)]];
  cpdef := [CharacteristicPolynomial(HeckeOperator(Sdef, P)) : P in Ps[1..Min(3, #Ps)]];
  assert cpind eq cpdef;
end for;
