/****************************************************************************
 * This file defines a class packaging together data attached to an ideal I
 * of a number field F which frequently get used together. 
 *
 * This serves to reduce repetition and simplify function signatures.
 **************************************************************************/

import "weight_rep.m" : GetOrMakeP1, matrix_of_induced_action;

declare type IdealDatum;
declare attributes IdealDatum:
  QuaternionOrder,
  FuchsianGroup,
  Ideal,
  IntegerRing,
  ResidueRing,
  Character,
  P1Elements,
  P1Rep,
  ResidueMap,
  CosetReps,
  CosetRepsByP1,
  InducedModuleMtrxs,
  H1s;

declare attributes GrpPSL2 : ideal_data;

forward Gamma0Cosets;

intrinsic cIdealDatum(
              Gamma::GrpPSL2, I::RngOrdIdl : 
              chi:=HeckeCharacterGroup(I, [1 .. Degree(NumberField(Order(I)))]).0
              ) -> IdealDatum
  {
    inputs:
      O - An order of a quaternion algebra B/F
      I - An ideal of the ring of integers Z_F of F
      chi::GrpHeckeElt - A Hecke character with modulus I

    Constructor.
  }
  if not assigned Gamma`ideal_data then
    Gamma`ideal_data := AssociativeArray();
    Gamma`ideal_data[I] := AssociativeArray();
  elif not IsDefined(Gamma`ideal_data, I) then
    Gamma`ideal_data[I] := AssociativeArray();
  elif IsDefined(Gamma`ideal_data[I], chi) then
    return Gamma`ideal_data[I][chi];
  end if;

  X := New(IdealDatum);
  X`FuchsianGroup := Gamma;
  X`Ideal := I;

  O := QuaternionOrder(Gamma);
  F := BaseField(Algebra(O));

  H := HeckeCharacterGroup(I, [1 .. Degree(F)]);
  assert Parent(chi) eq H;
  X`Character := chi;

  X`ResidueRing := quo<IntegerRing(X) | I>; 
  X`P1Elements, X`P1Rep := GetOrMakeP1(Gamma, I);
  _, X`ResidueMap := ResidueMatrixRing(O, I);

  if not (assigned Gamma`ShimFDSidepairsDomain and assigned Gamma`ShimFDDisc) then
    // assigns attributes of Gamma which are needed in Gamma0Cosets
    // this step can be slow
    _ := Group(Gamma);
  end if;

  X`CosetRepsByP1 := AssociativeArray();
  X`CosetReps := Gamma0Cosets(X);

  for i := 1 to #X`P1Elements do
    // TODO abhijitm these next three lines should be removed before committing,
    // they're just checks
    v := X`ResidueMap(X`CosetReps[i])[2];
    _, v := X`P1Rep(v, false, false);
    assert v eq X`P1Elements[i];

    // cache coset reps and their index in Gamma0Cosets
    // by their P1 representatives
    X`CosetRepsByP1[v] := <i, X`CosetReps[i]>;
  end for;
  assert #X`CosetRepsByP1 eq #X`P1Elements;

  X`InducedModuleMtrxs := AssociativeArray();
  X`H1s := AssociativeArray();

  Gamma`ideal_data[I][chi] := X;
  return X;
end intrinsic;

/***********************
 * Attribute access
 * ********************/

intrinsic IntegerRing(X::IdealDatum) -> Rng
  {}
  return Order(X`Ideal);
end intrinsic;

/**************************************
 * Coset representative computation
 * ***********************************/

function LeftToRightCosets(X)
  // X::IdealDatum
  //
  // Given a sequence of coset representatives for
  // Gamma(1) / Gamma(N), return a sequence of representatives
  // for Gamma(N) \ Gamma(1).
  rcosets := X`CosetReps;
  cosetsinv := [c^(-1) : c in rcosets];
  for c in cosetsinv do
    v := X`ResidueMap(c)[2];
    // Gamma`P1Ns[N] is a tuple, the second entry
    // is a map taking v to its standard representative
    // in P1N.
    _, v := X`P1Rep(v, false, false);
    rcosets[Index(X`P1Elements, v)] := c;
  end for;
  return rcosets;
end function;

function Gamma0Cosets(X : LeftCosets:=true)
  // X::IdealDatum
  //
  // returns a sequence of coset representatives Gamma(N) \ Gamma(1)

  Gamma := X`FuchsianGroup;
  N := X`Ideal;

  if not assigned Gamma`LevelCosets_new then
    Gamma`LevelCosets_new := AssociativeArray();
  end if;

  if IsDefined(Gamma`LevelCosets_new, N) then
    if LeftCosets then
      return Gamma`LevelCosets_new[N];
    else
      return LeftToRightCosets(X);
    end if;
  end if;

  if Norm(N) eq 1 then
    return [BaseRing(Gamma)!1];
  end if;

  vprintf ModFrmHil: "Computing cosets ..................................... ";
  time0 := Cputime();
  
  O := BaseRing(Gamma);
  B := Algebra(O);

  D := Parent(Gamma`ShimFDDisc[1]);
  mU := Gamma`ShimFDSidepairsDomain;
  i := 1;
  while i lt #mU do
    if mU[i] eq mU[i+1] then
      Remove(~mU,i);
    end if;
    i +:= 1;
  end while;
  mU := [<mU[i], i> : i in [1..#mU]];

  frontier := [<O!1,[]>];
  cosets := [<O!1,[Integers()|]> : i in [1..#X`P1Elements]];
  cosetcnt := 1;

  _, v := X`P1Rep(X`ResidueMap(O!1)[2], false, false);
  ind1 := Index(X`P1Elements, v);

  while frontier ne [] do
    newfrontier := [];
    for delta in frontier do
      for g in mU do
        gamma := delta[1]*g[1];

        v := X`ResidueMap(gamma)[2];
        _, v := X`P1Rep(v, false, false);
        ind := Index(X`P1Elements, v);
        if ind ne ind1 and cosets[ind][1] eq 1 then
          // Optionally, we could keep (and return) the elements in Gamma0N that
          // we find, but as it stands now, this wastes precious time as we
          // work with the induced module, anyway.
          cosets[ind] := <gamma, delta[2] cat [g[2]]>;
          Append(~newfrontier, <gamma, [g[2]] cat delta[2]>);
          cosetcnt +:= 1;
        end if;
      end for;
    end for;
    frontier := newfrontier;
  end while;

  if #Factorization(N) gt 0 then
    assert cosetcnt eq Norm(N)*&*[1+1/Norm(pp[1]) : pp in Factorization(N)];
  end if; 

  Gamma`LevelCosets_new[N] := [c[1] : c in cosets];
  vprintf ModFrmHil: "Time: %o\n", Cputime(time0);
  return Gamma0Cosets(X : LeftCosets:=LeftCosets);
end function;

function induced_module_mtrxs_of_gens(X, k)
  // X::IdealDatum
  // k::SeqEnum[RngIntElt]
  if IsDefined(X`InducedModuleMtrxs, k) then
    return X`InducedModuleMtrxs[k];
  end if;

  G, _, m := Group(X`FuchsianGroup);
  gens := [m(G.i) : i in [1 .. #Generators(G)]];

  Ms := AssociativeArray();
  for i in [1 .. #gens] do
    Ms[i] := matrix_of_induced_action(gens[i], k, X);
    Ms[-i] := matrix_of_induced_action(gens[i]^(-1), k, X);
  end for;

  X`InducedModuleMtrxs[k] := Ms;
  return Ms;
end function;
