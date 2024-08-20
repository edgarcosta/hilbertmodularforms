/******************************************************************************
* This file has tests for ModFrmHil/level.m::HeckeMatrix2, a modification of 
* !Geometry/ModFrmHil/level.m::HeckeMatrix.
*
* The tests ensure that the modifications do not break any existing behavior.
*******************************************************************************/

MAX_PP_NORM := 50;
NUM_TRIALS := 2;
OPTIONAL_TESTS := false;

// the default quaternion algebra is the one ramified at all but one infinite place
// this will thrwo an error if B over a field of even degree.
function test(F, N : B:=0)
  // F::FldNum
  // N::RngOrdIdl

  ZF := Integers(F);

  if B cmpeq 0 then
    B := QuaternionAlgebra(1*ZF, [InfinitePlaces(F)[i] : i in [2 .. Degree(F)]]);
  end if;

  assert BaseField(B) eq F;
  O := MaximalOrder(B);
  D := Discriminant(B);
  // the level and discriminant are assumed to be coprime
  assert IsCoprime(N, D);

  Gamma := FuchsianGroup(O);

  // Hecke matrix at infinity
  assert HeckeMatrix(Gamma, N, "Infinity") eq HeckeMatrix2(Gamma, N, "Infinity");
  d := Nrows(HeckeMatrix(Gamma, N, "Infinity"));

  coprime_pps := [pp : pp in PrimesUpTo(MAX_PP_NORM, F) | GCD(pp, N * D) eq 1*ZF];
  level_pps := [fac[1] : fac in Factorization(N)];
  disc_pps := [fac[1] : fac in Factorization(Discriminant(B))];

  for _ in [1 .. NUM_TRIALS] do
    pp := Random(coprime_pps);
    assert HeckeMatrix(Gamma, N, pp) eq HeckeMatrix2(Gamma, N, pp);

    if #level_pps ne 0 then
      pp := Random(level_pps);
      assert HeckeMatrix(Gamma, N, pp) eq HeckeMatrix2(Gamma, N, pp);
      assert HeckeMatrix(Gamma, N, pp : UseAtkinLehner:=true) eq HeckeMatrix2(Gamma, N, pp : UseAtkinLehner:=true);
      Exclude(~level_pps, pp);
    end if;

    if #disc_pps ne 0 then
      pp := Random(disc_pps);
      assert HeckeMatrix(Gamma, N, pp : UseAtkinLehner:=true) 
        eq HeckeMatrix2(Gamma, N, pp : UseAtkinLehner:=true);
      Exclude(~disc_pps, pp);
    end if;
  end for;
  return d;
end function;

R<x> := PolynomialRing(Rationals());

// h+(F) = 1, D = 1, N = 4
F := NumberField(x^3-x^2-2*x+1);
ZF := Integers(F);
// the dimension of H1 is 2, see Greenberg-Voight
assert test(F, 4*ZF) eq 2;

// h+(F) = 1, D = 1, N = (7, a)^2 * (2)
pps := PrimesUpTo(15, F);
_ := test(F, pps[1]^2 * pps[2]);

// h+(F) = 1, D = (2) * (13, alpha), N = (7, a) * (2)
B := QuaternionAlgebra(2 * Factorization(13*ZF)[1][1], [InfinitePlaces(F)[i] : i in [2 .. Degree(F)]]);
_ := test(F, Factorization(7*ZF)[1][1] : B:=B);

// h+(F) = 3, D = 1
F := NumberField(x^3-x^2-9*x+8);
ZF := Integers(F);
pps := PrimesUpTo(15, F);
_ := test(F, pps[1] * pps[2]);

if OPTIONAL_TESTS then
  // h+(F) = 1, D = 1, N = 1
  F := NumberField(x^3-x^2-10*x+8);
  ZF := Integers(F);
  // the dimension of H1 is 4, see Greenberg-Voight
  assert test(F, 1*ZF) eq 4;

  // h+(F) = 1, D = 1, N = 3
  _ := test(F, 3*ZF);

  // h+(F) = 2, D = 1
  F := NumberField(x^3-x^2-9*x+10);
  ZF := Integers(F);
  _ := test(F, 2*ZF);
end if;

