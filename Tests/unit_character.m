// code for testing computation of unit characters

/********************** Helper code **********************/

PREC := 10;

procedure test(M, k, correct : level := 1, chi := 1)
  /***
   * M::ModFrmHilDGRng 
   * k::SeqEnum[RngIntElt]
   * correct::Assoc[RngOrdIdl -> Assoc[RngOrdElt -> FldNumElt]]
   * level::RngOrdIdl
   * chi::GrpHeckeElt
   ***/

  F := BaseField(M);
  N := (level cmpeq 1) select 1*Integers(F) else level;
  H := HeckeCharacterGroup(N, [1 .. Degree(F)]);
  chi := H!chi;

  Mk := HMFSpace(M, N, k, chi);
  unit_chars := Mk`UnitCharacters;

  // there should be one unit character for each component
  assert #unit_chars eq NarrowClassNumber(F);

  for bb in NarrowClassGroupReps(M) do
    uc :=  Mk`UnitCharacters[bb];
    for eps in TotallyPositiveUnitsGenerators(F) do
      computed := Evaluate(uc, eps);
      actual := correct[bb][eps];
      if computed ne actual then
        print "Error!";
        // TODO abhijitm indents in this print statement
        // are busted whyyyyy
        printf "At bb = %o, the computed evaluation of the
        unit character on eps = %o was %o but the true value
        is %o\n", IdealOneLine(bb), eps, computed, actual;
      end if;
      assert computed eq actual;
    end for;
  end for;
end procedure;

/********************** Q(sqrt(5) **********************/

F := QuadraticField(5);
ZF := Integers(F);
prec:= PREC;
M := GradedRingOfHMFs(F, prec);
eps := TotallyPositiveUnitsGenerators(F)[1];
correct := AssociativeArray();
bb := 1*ZF;
correct[bb] := AssociativeArray();

//////////////////////// k = [2,2] /////////////////////////
// parallel weight

k := [2,2];
K := UnitCharField(F, k);

// in parallel weight the unit character 
// should be trivial
correct[bb][eps] := K!1;
test(M, k, correct);

//////////////////////// k = [2,4] /////////////////////////
// nonparallel weight

k := [2,4];
K := UnitCharField(F, k);
auts := AutsOfUCFReppingEmbeddingsOfF(F, k);

// eps_1^(k_1/2) * eps_2^(k_2/2) = eps_1 * eps_2^2 = N(eps) * eps_2
// If [sigma_1, sigma_2] is the output of EmbeddingsIntoUnitCharField and
// [v_1, v_2] is a list of places then this is also equal to
// v_1(sigma_2(eps)). The coefficient we store internally should be
// sigma_2(eps).
correct[bb][eps] := auts[2](eps);
test(M, k, correct);

//////////////////////// k = [3,2] /////////////////////////
// nonparitious weight

k := [3,2];
N := 11*ZF;
H := HeckeCharacterGroup(N, [1,2]);
chi := H.1; // character of order 11
K := UnitCharField(F, k);
//
// eps_1^(k_1/2) * eps_2^(k_2/2) = eps_1^(3/2) * eps_2 = eps_1^(1/2)
// The coefficient we store should thus be the positive square root
// of eps_1. eps = mu^2 for mu = +/- (1-sqrt(5))/2 (under v_1, say).
// We want the one which is positive under v_1, so -(1-sqrt(5))/2.
v_0 := MarkedEmbedding(K);
correct[bb][eps] := K!(ZF.2-1);
test(M, k, correct : level:=N, chi:=chi);

////********************** Q(sqrt(3) **********************////

F := QuadraticField(3);
ZF := Integers(F);
prec:= PREC;
M := GradedRingOfHMFs(F, prec);
eps := TotallyPositiveUnitsGenerators(F)[1];
correct := AssociativeArray();
for bb in M`NarrowClassGroupReps do
  correct[bb] := AssociativeArray();
end for;

// parallel weight
k := [5,5];
K := UnitCharField(F, k);

for bb in M`NarrowClassGroupReps do
  correct[bb][eps] := K!1;
end for;
test(M, k, correct);

////********************** Galois cubic with discriminant 49 **********************////

// weight [2,2,2] over a Galois cubic field 

R<x> := PolynomialRing(Rationals());
F<a> := NumberField(x^3 - x^2 - 2*x + 1);
ZF := Integers(F);
prec:=20;
M := GradedRingOfHMFs(F, prec);
// there should be one unit character for each component

correct := AssociativeArray();
for bb in M`NarrowClassGroupReps do
  correct[bb] := AssociativeArray();
end for;

U, m := UnitGroup(F);
eps_1 := m(U.1);
eps_2 := m(U.2);
bb := 1*ZF;

k := [2,2,2];
K := UnitCharField(F, k);
for eps in TotallyPositiveUnitsGenerators(F) do
  correct[bb][eps] := K!1;
end for;

test(M, k, correct);

k := [2,2,4];
K := UnitCharField(F, k);
auts := AutsOfUCFReppingEmbeddingsOfF(F, k);
for eps in TotallyPositiveUnitsGenerators(F) do
  // this is the same as auts[1](eps) * auts[2](eps) * auts[3](eps)^2
  // because Norm(eps) = 1.
  correct[bb][eps] := auts[3](eps);
end for;

test(M, k, correct);

k := [2,2,3];
K := UnitCharField(F, k);
// because h+(F) = 1, every totally positive unit is a square,
// so the image of the unit character actually lies in F
assert IsIsomorphic(K, F); 
auts := AutsOfUCFReppingEmbeddingsOfF(F, k);
for eps in TotallyPositiveUnitsGenerators(F) do
  // this is the same as auts[3](eps)^(1/2), and it should be 
  // the positive square root
  x := Sqrt(auts[3](eps));
  // we want the square root to be a "positive real number", and since we can archimedean-ize everything
  // by embedding using the marked embedding, this means that we want 
  x *:= Sign(Evaluate(StrongCoerce(F, x), MarkedEmbedding(F)));
  correct[bb][eps] := x;
end for;

/********************** non-Galois cubic with discriminant -23 **********************////

// weight [2,3,4] over the non-Galois cubic field 
// with defining polynomial x^3 - 21 x - 28
// this captures all the complications of the
// earlier tests

