
import "ModFrmHil/copypaste/hecke.m" : hecke_algebra;

declare type HMFCache;
declare type EigenformCache;

// TODO:
// - EigenformCache to string
// - read EigenformCache from string

declare attributes EigenformCache:
  Parent, // HMFCache
  Origin, // MdmFrm
  Weight, // Eltseq
  Character, // ?
  Level, // RngOrdIdl
  LinearCombination, // Assoc(), primes -> coefficients
  // where Tzeta == &+[Tp(f)*c where p := primes[i]] : i->c in coefficients];
  RationalForm, // _, S, _ := RationalForm(Tzeta),
  HeckeOperators; // Assoc(), p -> S*HeckeOperator(f, p)*S^-1


declare attributes HMFCache:
  BaseField, // FldNum, the internal basefield
  ToBaseField, // Map, from InputBasefield to BaseField
  Primes, // SeqEnum[RngOrdIdl] primes up to some bound, expandable when necessary
  PrimesDict, // Assoc, Primes[i] -> i
  CharacterCoordinates, // Assoc, N -> [i] such that characters psi(p_i) determines psi
  Eigenforms, // Assoc
  // <k, N, chi> -> [ EigenformCache(f) : f in NewformDecomposition ]
  filename; // MonStgElt


function NormPrimesBound(C)
  return Norm(C`Primes[#C`Primes]);
end function;

function IncreasePrimes(~C : up_to:=false)
  current := NormPrimesBound(C);
  if up_to cmpeq false then
    // not the best, but should work for our purposes
    up_to +:= NormPrimesBound(C) + 100*Degree(BaseField(C))*Floor(Log(100*Degree(Basefield(C))));
  end if;
  if up_to gt current then
    new_primes := PrimesUpTo(up_to, BaseField(C));
    old_count := #C`primes;
    assert Set(new_primes[old_count]) eq Set(C`primes);
    C`Primes cat:= new_primes[old_count + 1 .. #new_primes];
    for i->p in [old_count..#C`Primes] do
      C`PrimesDict[p] := i;
    end for;
  end if;
end function;

function EltseqRows(M)
  return [Eltseq(r) : r in Rows(M)];
end function;


intrinsic EigenformCacheInitialize() -> HMFCache
{ Create an empty EigenformCache object }
  C := New(HMFCache);
  return C;
end intrinsic;

intrinsic Parent(C:EigenformCache) -> HMFCache
{ return the parent of the eigenform cache structure }
  return C`Parent;
end intrinsic;

intrinsic Origin(C:EigenformCache) -> HMFCache
{ return the original eigenform for the eigenform cache structure }
  return C`Origin;
end intrinsic;

intrinsic Weight(C:EigenformCache) -> HMFCache
{ return the weight of the eigenform in the cache structure }
  return C`Weight;
end intrinsic;

intrinsic Character(C:EigenformCache) -> HMFCache
{ return the character of the eigenform in the cache structure }
  return C`Character;
end intrinsic;

intrinsic Level(C:EigenformCache) -> HMFCache
{ return the level of the eigenform in the cache structure }
  return C`Level;
end intrinsic;


intrinsic LinearCombination(C:EigenformCache) -> Assoc
{ return the LinearCombination for the eigenform cache structure }
  return C`LinearCombination;
end intrinsic;

intrinsic HeckeOperators(C:EigenformCache) -> Assoc
{ return the HeckeOperators associative array }
  return C`HeckeOperators;
end intrinsic;

intrinsic UpdateHeckeOperators(~C:EigenformCache)
{ update the cached table from the magma form }
  if not Origin(C) cmpeq false then
    if assigned Origin(C)`Hecke then
      S := RationalForm(C);
      f := Origin(C);
      for p in Keys(HeckeOperators(C)`Hecke) diff Keys(HeckeOperators(C)) do
        C`HeckeOperators[p] := S*HeckeOperator(p)*S^-1;
      end for;
      // this is non-empty due to LinearCombination being a non-emtpy assoc
      max_norm := Max([Norm(elt) : elt Keys(HeckeOperators(C)) join Keys(LinearCombination(C))]);
      P := Parent(C);
      IncreasePrimes(~C : up_to:=max_norm);
    end if;
  end if;
end intrinsic;




intrinsic Record(C:EigenformCache) -> SeqEnum[MonStgElt]
  { return string represeting MachinePrint }
  /*
  - Weight
  - Level
  - Character
  - primitive generator
  - rational form // do we really need this?
  - hecke with respect to zeta
  */
  P := Parent(C);

  res := [
    MachinePrint(Weight(C)),
    MachinePrint(Level(C)),
    MachinePrint([CharacterCoordinates(P, psi), ValuesOnCoordinates(P, psi)]) where psi := Character(C),
  ];


  primes := Primes(P);
  primes_dict := PrimesDict(P);

  lc := LinearCombination(C);
  prime_coordinates := [primes_dict[p] : p in Keys(lc)];
  zeta_coeffs := [lc[primes[i]] : i in prime_coordinates];
  Append(~res, MachinePrint([prime_coordinates, zeta_coeffs]));

  Append(~res, MachinePrint(EltseqRows(RationalForm(C))));

  ho := HeckeOperators(C);
  primes_hecke := [primes_dict[i] : i in Keys(ho)];
  hecke_operators := [EltseqRows(ho[primes[i]]) : i in primes_hecke];
  Append(~res, MachinePrint([primes_hecke, hecke_operators]));
  return res;
end intrinsic;

intrinsic CacheEigenform(~P::HMFCache, f:ModFrmHil)
  {  }
  C := EigenformCacheInitialize();
  C`Parent := P;
  C`Origin := f;
  C`Weight := Weight(f);
  C`Level := Level(f);
  C`Character := Character(f);
  _ := hecke_algebra(f: generator:=true);
  _ , primes_used, _, _, _, Tzeta, linear_combination := Explode(f`hecke_algebra);
  C`LinearCombination := AssociativeArray();
  for i->p in primes_used do
    C`LinearCombination[p] := linear_combination[i];
  end for;
  _, C`RationalForm, _ := RationalForm(Tzeta);
  C`HeckeOperators := AssociativeArray();
  t := <Weight(C), Weight(C), Character(C)>;
  if not IsDefined(P`Eigenforms, t) then
    P`Eigenforms[t] := [];
  end if;
  // we don't make any check if the form is already there!
  Append(~P`Eigenforms[t], C);
end intrinsic;

intrinsic ReadEigenformCache(~P::HMFCache, s::SeqEnum[MonStgElt])
  { }
  assert #s eq 6
  C := EigenformCacheInitialize();
  C`Parent := P;
  C`Origin := false;
  C`Weight := StringToArrayOfArraysOfIntegers(s[1]);
  C`LeveL := ideal< Integers(BaseField(P)) | StringToArrayOfArraysOfIntegers(s[2]) >;
  // TODO
end intrinsic;

/*
 * TODO:
 * - convert from magma gen to stored gen
 * - save hecke_gen_*
 */
intrinsic BaseField(C::HMFCache) -> FldNum
{ return the internal BaseField for the cache structure}
  return C`BaseField;
end intrinsic;


intrinsic Primes(C::HMFCache) -> SeqEnum[RngOrdIdl]
{ return the current list of primes for the cache structure}
  return C`Primes;
end intrinsic;

intrinsic PrimesDict(C::HMFCache) -> SeqEnum[RngOrdIdl]
{ return the current list of primes for the cache structure}
  return C`PrimesDict;
end intrinsic;




intrinsic HMFCacheInitialize() -> HMFCache;
  {Create an empty HMFCache object}
  C := New(HMFCache);
  return C;
end intrinsic;

intrinsic ToBaseField(C::HMFCache, I::RngOrdIdl) -> RngOrdIdl
  if not assigned C`ToBaseField then
    b, C`ToBaseField := IsIsomorphic(NumberField(Order(I)));
    require b : "The stored base field is not isomorphic to the input base field.";
  end if;
  return ChangeRing(I, C`ToBaseField);
end intrinsic;





intrinsic HMFCache(filename::MonStgElt) -> HMFCache
  {Load HMFCache from a file}
  C := HMFCacheInitialize();
  C`filename := filename;
  C`InputBasefield := false;
  records := ReadRecords(filename);
  /*
  - field:primes
    - field SeqEnum[RngIntElt]
    - primes SeqEnum[SeqEnum[RngIntElt]]
    - k:N:chi_coord:chi_values:hecke_gen_primes:hecke_gen_coeffs:prime indexes:hecke_matrix
    - k RngIntElt
    - N SeqEnum[RngIntElt]
    // representing chi by evaluating it at a subset of the primes
    - chi_coord SeqEnum[RngIntElt]
    - chi_values SeqEnum[RngIntElt]
    // the hecke generator
    - hecke_gen_primes SeqEnum[RngIntElt]
    - hecke_gen_coeffs SeqEnum[RngIntElt]
    // list primes for which we have the Hecke operator
    - prime indexes SeqEnum[RngIntElt]
    // representing the Hecke operator at p[i] in the
    // basis for the rational form of the generator
    - eigenvalues SeqEnum[SeqEnum[RngIntElt]]
  */


  R<x> := PolynomialRing(Integers());
  F<a> := NumberField(R!StringToArrayOfIntegers(records[1][1]));
  ZF := Integers(F);
  C`Primes := [ ideal<ZF! [F!elt : elt in gens]> : gens in StringToArrayOfArraysOfIntegers(records[1][2]) ];
  C`Eigenforms := AssociativeArray();
  for rec in records[2..#records] do
    k, N, L, ind, ap := Explode(rec);
    k := StringToInteger(k);
    N := ideal<ZF|[ZF!elt : elt in StringToArrayOfIntegers(Nstr)]>;
    pair := <k, N>;
    L := NumberField(R!StringToArrayOfIntegers(L));
    ind := StringToArrayOfIntegers(ind);
    ap := [L!elt : elt in StringToArrayOfArraysOfRationals(ap)];
    assert #ind eq #ap;
    ap_map := AssociativeArray();
    for i in [1..#ind] do
      ap_map[primes[ind[i]]] := ap[i];
    end for;
    if not IsDefined(C`Eigenforms, pair) then
      C`Eigenforms[pair] := []
    end if;
    Append(~C`Eigenforms[pair], <L, ap_map>);
  end for;
  C`Primes := SetToIndexedSet(SequenceToSet(C`Primes));
  return C;
end intrinsic;




function IsFaithful(characters, values, indices)
  return #Set(Rows(Transpose(Matrix(Columns(values, indices))))) eq #characters
end function;


intrinsic CharacterCoordinates(C::HMFCache, psi::GrpHeckeElt) -> SeqEnum[RngIntElt]
{ returns the index of the primes that we can use to distinguish characters with the same modulus }
  modulus := Modulus(psi);
  b, val := IsDefined(CharacterCoordinates, modulus);
  if not b then
    F := BaseField(C);
    H := HeckeCharacterGroup(modulus, [1..#Degree(F)]);
    characters := Elements(H);
    primes := Primes(C);
    values := Matrix([['@'(p, psi : Raw := true) : p in primes] : psi in characters]);
    ind := PivotColumns(Matrix(values));
    i := 1;
    while not IsFaithful(characters, values, ind) do
      IncreasePrimes(~C);
      primes := Primes(C);
      values := Matrix([['@'(p, psi : Raw := true) : p in primes] : psi in characters]);
      ind := PivotColumns(Matrix(values));
      i +:= 1;
      assert i lt 100;
    end while;
    CharacterCoordinates[modulus] := ind;
    val := ind;
  end if;
  return val;
end intrinsic;


intrinsic ValuesOnCoordinates(C::HMFCache, psi::GrpHeckeElt) -> SeqEnum[RngIntElt]
{ return the [Log(psi(p), zeta) : p in Primes(C)[CharacterCoordinates(level, order)]] }
  return [Integers()!'@'(p, psi : Raw := true) : p in primes] where primes := CharacterCoordinates(C, psi);
end intrinsic;




intrinsic Save(C::HMFCache, filename::MonStgElt) -> RngIntElt
  {Save the given object to a file}

  // field:primes
  records := [[
    Sprint(ElementToSequence(C`BaseField)),
    ElementToSequence(ElementToSequence(C`Primes))
  ]];

  ef := [];
  for kNchi->efs in C`Eigenforms do
  // k:N:chi_coord:chi_values:coeff field:prime indexes:eigenvalues
    k, N, chi := Explode(kNchi);
    k := Sprint(k);
    N := Sprint(ElementToSequence(N));
    chi_coord := Sprint(CharacterCoordinates(chi));
    chi_values := Sprint(ValuesOnCoordinates(chi));

    for ef in efs do
      field, evmap := Explode(efs);
      field := Sprint(ElementToSequence(field));
      ind := [];
      ev := [];
      for i->p in Primes(C) do
        b, val := IsDefined(evmap, p);
        if b then
          Append(~ind, i);
          Append(~ev, val);
        end if;
      end for;
      ind := Sprint(ind);
      ev := Sprint(ElementToSequence(ev));
      Append(~records, [k, N, field, ind, ev]);
    end for;
  end for;
  return WriteRecords(filename, records);
end intrinsic;


intrinsic MatchEigenforms(C::HMFCache, list::List) -> SeqEnum[RngIntElt]
  { return the permutation matching the eigenvalues cached and list of eigenforms }
  if #list eq 0 then
    return [];
  end for;
  origLevel := Level(Parent(list[1]));
  N := ToBaseField(C, origLevel);
  k := Weight(Parent(list[1]));
  require #SequenceToSet(k) eq 1: "What? Now we can handle non parallel weight? ＼(＾O＾)／";
  k := k[1];
  pair := <k, N>;
  // the easy case
  if not IsDefined(C`Eigenforms, <k, N>) then
    C`Eigenforms[<k, N>] := [<BaseField(elt), AssociativeArray()> : elt in list];
    return [1..#list];
  end if;
  cached_eigenforms := C`Eigenforms[<k, N>];
  require #cached_eigenforms eq #list : "the number of stored eigenforms doesn't match";
  res := [];
  left := [i : in [1..#list]];
  for i->f in list do
    // first filter by degree
    candidates := [i : i in left | Degree(BaseField(elt)) eq Degree(cached_eigenforms[i][1]) ];
    // then by isomorphism
candidates := 
  end for;
end intrinsic;

