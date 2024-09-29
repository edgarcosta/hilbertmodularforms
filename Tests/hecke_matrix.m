/******************************************************************************
* This file has tests for ModFrmHil/level.m::HeckeMatrix2, a modification of 
* !Geometry/ModFrmHil/level.m::HeckeMatrix.
*
* The tests ensure that the modifications do not break any existing behavior.
*******************************************************************************/

MAX_PP_NORM := 50;
OPTIONAL_TESTS := false;

// set to true if you want to print times
PRINT_TIMES := true;

import "./ModFrmHil/ideal_datum.m" : induced_module_mtrxs_of_gens;

forward RightPermutationActions;


// Gamma`LevelRPAs_new stores a dictionary keyed by level N.
// Gamma`LevelRPAs_new[N] contains a dictionary keyed by 
// the integers [-#gens ..., -1, 1, ..., #gens], where gens is
// Generators(Group(Gamma)).
//
// At a positive integer i, the dictionary stores the permutation matrix 
// induced by right action of the ith generator on coset representatives
// (which should be something like Gamma(N) \ Gamma). 
function RightPermutationActions(X)
  // X::IdealDatum
  Gamma := X`FuchsianGroup;
  N := X`Ideal;
  time0 := Cputime();

  U, m := Group(Gamma);
  RPAs := AssociativeArray();
  for i := 1 to #Generators(U) do
    delta := Quaternion(m(U.i));
    perm := [];
    for alphai in X`CosetReps do
      _, v := X`P1Rep(X`ResidueMap(alphai*delta)[2], false, false);
      Append(~perm, Index(X`P1Elements, v));
    end for;
    RPAs[i] := PermutationSparseMatrix(Integers(), SymmetricGroup(#X`P1Elements)!perm);
    RPAs[-i] := PermutationSparseMatrix(Integers(), SymmetricGroup(#X`P1Elements)!perm^-1);
  end for;

  vprintf ModFrmHil: "Time: %o\n", Cputime(time0);
  return RPAs;
end function;

// compares HeckeMatrix(Gamma, N, pp) to HeckeMatrix2(Gamma, N, pp)
// and optionally returns the duration of HeckeMatrix2.

// Note that the first iteration of HeckeMatrix in each test() may be
// very slow if a presentation for Gamma needs to be computed. Once this
// is computed it is cached and subsequent runs can be meaningfully
// compared.
procedure compare_and_time(Gamma, N, pp, k : UseAtkinLehner:=false)
  F := BaseField(QuaternionAlgebra(Gamma));

  t := Cputime();
  M2 := HeckeMatrix2(Gamma, N, pp, k, 1 : UseAtkinLehner:=UseAtkinLehner);
  hm2_time := Cputime(t);

  M := HeckeMatrix(Gamma, N, pp : UseAtkinLehner:=UseAtkinLehner);

  if #SequenceToSet(k) eq 1 and k[1] eq 2 then
    assert M eq M2;
  end if;

  if PRINT_TIMES then
    print "HeckeMatrix2 time: ", hm2_time;
    print "\n";
  end if;
end procedure;


// the default quaternion algebra is the one ramified at all but one infinite place
// this will throw an error if B over a field of even degree.
procedure test(F, N : B:=0)
  // F::FldNum
  // N::RngOrdIdl

  if PRINT_TIMES then
    print "-----------------------------------------------\n";
  end if;

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

  X := cIdealDatum(Gamma, N);
  // because HeckeMatrix only works in parallel weight, this is the setting
  // in which we test
  k := [2 : _ in [1 .. Degree(F)]];

  assert [<a, b> : a->b in induced_module_mtrxs_of_gens(X, k)] eq 
              [<a, b> : a->b in RightPermutationActions(X)];

  // Hecke matrix at infinity
  compare_and_time(Gamma, N, "Infinity", k);

  coprime_pps := [pp : pp in PrimesUpTo(MAX_PP_NORM, F) | GCD(pp, N * D) eq 1*ZF];
  level_pps := [fac[1] : fac in Factorization(N)];
  disc_pps := [fac[1] : fac in Factorization(Discriminant(B))];

  pp := coprime_pps[3];
  compare_and_time(Gamma, N, pp, k);

  if #level_pps ne 0 then
    pp := level_pps[1];
    compare_and_time(Gamma, N, pp, k);
    compare_and_time(Gamma, N, pp, k : UseAtkinLehner:=true);
    Exclude(~level_pps, pp);
  end if;

  if #disc_pps ne 0 then
    pp := disc_pps[1];
    compare_and_time(Gamma, N, pp, k : UseAtkinLehner:=true);
    Exclude(~disc_pps, pp);
  end if;
end procedure;

R<x> := PolynomialRing(Rationals());

// h+(F) = 1, D = 1, N = 4
F := NumberField(x^3-x^2-2*x+1);
ZF := Integers(F);

test(F, 4*ZF);

// h+(F) = 1, D = 1, N = (7, a)^2 * (2)
pps := PrimesUpTo(15, F);
test(F, pps[1]^2 * pps[2]);

// h+(F) = 1, D = (2) * (13, alpha), N = (7, a)
B := QuaternionAlgebra(2 * Factorization(13*ZF)[1][1], [InfinitePlaces(F)[i] : i in [2 .. Degree(F)]]);
test(F, Factorization(7*ZF)[1][1] : B:=B);


if OPTIONAL_TESTS then
  // h+(F) = 3, D = 1
  F := NumberField(x^3-x^2-9*x+8);
  ZF := Integers(F);
  pps := PrimesUpTo(15, F);
  test(F, pps[1] * pps[2]);

  // h+(F) = 1, D = 1, N = 1
  F := NumberField(x^3-x^2-10*x+8);
  ZF := Integers(F);
  // the dimension of H1 is 4, see Greenberg-Voight
  test(F, 1*ZF);

  // h+(F) = 1, D = 1, N = 3
  test(F, 3*ZF);

  // h+(F) = 2, D = 1
  F := NumberField(x^3-x^2-9*x+10);
  ZF := Integers(F);
  test(F, 2*ZF);
end if;

// tests for new functionality

F := NumberField(x^3-x^2-2*x+1);
ZF := Integers(F);
B := QuaternionAlgebra<F | -F.1^2 + F.1 - 1, -8*F.1^2 + 4*F.1 + 16>;
O := MaximalOrder(B);
D := Discriminant(B);
Gamma := FuchsianGroup(O);

// test for nontrivial nebentypus 

N := 3*ZF;
chi := HeckeCharacterGroup(N, [1,2,3]).1;
k := [3,3,3];
pp := 2*ZF;

T2chi, lambdas_2 := HeckeMatrix2(Gamma, N, pp, k, chi);
assert #lambdas_2 eq 1;
assert Norm(lambdas_2[1]) eq 8;
assert R!CharacteristicPolynomial(T2chi) eq (x^6 + 490*x^4 + 60025*x^2);

// test for nonparallel weight

N := 2*ZF;
k := [4,4,4];
pp := Factorization(7*ZF)[1][1];
T7, lambdas_7 := HeckeMatrix2(Gamma, N, pp, k, 1);
assert #lambdas_7 eq 1;
assert Norm(lambdas_7[1]) eq 7;
assert R!CharacteristicPolynomial(T7) eq (x^8 - 16*x^7 - 2624*x^6 + 34048*x^5 + 2584064*x^4 - 23883776*x^3 - 1140801536*x^2 + 5507317760*x + 192756121600);

// TODO abhijitm add examples for nontrivial class number,
// nonparitious weight, and more!
