declare type EigenvaluesCache;

declare attributesEigenvaluesCache:
  BaseField, // FldNum, the internal basefield
  ToBaseField, // Map, from InputBasefield to BaseField
  Primes, // SeqEnum[RngOrdIdl] primes up to some bound, expandable when necessary
  CharacterCoordinates, // Assoc, <N, order> -> [i] such that characters psi(p_i) determines psi
  Eigenforms, // Assoc, <k, N, chi> -> [ <primes_used, coefficients, p -> T_p(f) > : f in NewformDecomposition ]
  // where Tzeta = is the single generator the Hecke algebra
  // and Tzeta == &+[Tp(f)*c where p := Primes[primes_used[i]]) : i->c in coefficients];
  // and Tp(f) = S*HeckeOperator(M)*S^-1 where _, S, _ := RationalForm(Tzeta)
  filename; // MonStgElt


/*
 * TODO:
 * - convert from magma gen to stored gen
 *
 */
intrinsic BaseField(C::EigenvaluesCache) -> FldNum
{ return the internal BaseField for the cache structure}
  return C`BaseField;
end intrinsic;


intrinsic Primes(C::EigenvaluesCache) -> SeqEnum[RngOrdIdl]
{ return the current list of primes for the cache structure}
  return C`Primes;
end intrinsic;

function IncreasePrimes(C : increase_bound := 100)
  current_bound := C`Primes[#C`Primes];
  new_primes := PrimesUpTo(current_bound + increase_bound, BaseField(C);
  assert Set(new_primes[#C`primes]) eq Set(C`primes);
  C`Primes cat := new_primes[#C`Primes + 1 .. #new_primes];
  return C`Primes;
end funcion;


intrinsic CharacterCoordinates(C::EigenvaluesCache, level::RngOrdIdl, order::RngIntElt) -> SeqEnum[RngIntElt]
{ TODO }
  if not IsDefined(CharacterCoordinates, <level, order>)
    F := BaseField(C);
    H := HeckeCharacterGroup(F, [1..#Degree(F)]);
    characters := [elt : elt in Elements(H) | Order(elt) eq  order];
    //Reduce target ring
    CF := CyclotomicField(order);
    zeta := CF.1;
    for i in [1..#characters] do
        SetTargetRing(~characters[i], zeta);
    end for;
  primes := Primes(C);
  values := Matrix([[psi(p) : p in primes] : psi in characters]);
  ind := PivotColumns(Matrix(values));
  while #Set(Columns(M, ind)) ne #ind do
    primes := IncreasePrimes(C);
    values := Matrix([[psi(p) : p in primes] : psi in characters]);
    ind := PivotColumns(Matrix(values));
  end while;
  CharacterCoordinates[<N, o>] := ind;
  return CharacterCoordinates[<N, o>];
end if;


intrinsic EigenvaluesCacheInitialize() -> EigenvaluesCache;
  {Create an empty EigenvaluesCache object}
  C := New(EigenvaluesCache);
  return C;
end intrinsic;

intrinsic ToBaseField(C::EigenvaluesCache, I::RngOrdIdl) -> RngOrdIdl
  if not assigned C`ToBaseField then
    b, C`ToBaseField := IsIsomorphic(NumberField(Order(I)));
    require b : "The stored base field is not isomorphic to the input base field.";
  end if;
  return ChangeRing(I, C`ToBaseField);
end intrinsic;

intrinsic EigenvaluesCache(filename::MonStgElt) -> EigenvaluesCache
  {Load EigenvaluesCache from a file}
  C := EigenvaluesCacheInitialize();
  C`filename := filename;
  C`InputBasefield := false;
  records := ReadRecords(filename);
  /*
  - field:primes
    - field SeqEnum[RngIntElt]
    - primes SeqEnum[SeqEnum[RngIntElt]]
    - k:N:chi_order:chi:coeff field:prime indexes:eigenvalues
    - k RngIntElt
    - N SeqEnum[RngIntElt]
    - chi //FIXME
    - coeff field SeqEnum[RngIntElt]
    - prime indexes SeqEnum[RngIntElt]
    - eigenvalues SeqEnum[SeqEnum[RngIntElt]]
  */


  R<x> := PolynomialRing(Integers());
  F<a> := NumberField(R!StringToArrayOfIntegers(records[1][1]));
  ZF := Integers(F);
  C`Primes := [ ideal<ZF! [F!elt : elt in gens]> : gens in StringToArrayOfArraysOfIntegers(records[1][2]) ];
  C`EigenForms := AssociativeArray();
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
    if not IsDefined(C`EigenForms, pair) then
      C`EigenForms[pair] := []
    end if;
    Append(~C`EigenForms[pair], <L, ap_map>);
  end for;
  C`Primes := SetToIndexedSet(SequenceToSet(C`Primes));
  return C;
end intrinsic;


intrinsic Save(C::EigenvaluesCache, filename::MonStgElt) -> RngIntElt
  {Save the given object to a file}

  // field:primes
  records := [[
    Sprint(ElementToSequence(C`BaseField)),
    ElementToSequence(ElementToSequence(C`Primes))
  ]];

  ef := [];
  for kNchi->efs in C`EigenForms do
    // k:N:chi:coeff field:prime indexes:eigenvalues
    k, N, chi := Explode(kNchi);
    k := Sprint(k);
    N := Sprint(N);
    chi := Sprint(chi);

    for ef in efs do
      field, evmap := Explode(efs);
      field := Sprint(ElementToSequence(field));
      ind := [];
      ev := [];
      for i in [1..#C`primes] do
        if IsDefined(evmap, C`primes[i]) then
          Append(~ind, i);
          Append(~ev, evmap[C`primes[i]]);
        end if;
      end for;
      ind := Sprint(ind);
      ev := Sprint(ElementToSequence(ev));
      Append(~records, [k, N, field, ind, ev]);
    end for;
  end for;
  return WriteRecords(filename, records);
end intrinsic;


intrinsic MatchEigenforms(C::EigenvaluesCache, list::List) -> SeqEnum[RngIntElt]
  {TODO}
  if #list eq 0 then
    return [];
  end for;
  origLevel := Level(Parent(list[1]));
  N := ToBaseField(C, origLevel);
  k := Weight(Parent(list[1]));
  require #SequenceToSet(k) eq 1: "What? Now we can handle non parallel weight?";
  k := k[1];
  pair := <k, N>;
  // the easy case
  if not IsDefined(C`EigenForms, <k, N>) then
    C`EigenForms[<k, N>] := [<BaseField(elt), AssociativeArray()> : elt in list];
    return [1..#list];
  end if;
  require #C`EigenForms[<k, N>] eq #list : "the number of stored eigenforms doesn't match";
  res := [];
  left := [i : in [1..#list]];
  for f in list do
    for elt in  do
    end for;
    candidates := [i : i in [1
  end for;
end intrinsic;

