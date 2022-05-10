declare type EigenvaluesCache;

declare attributesEigenvaluesCache:
  BaseField, // FldNum, the internal basefield
  ToBaseField, // Map, from InputBasefield to BaseField
  Primes, // SeqEnum[RngOrdIdl] primes up to some bound, expandable when necessary
  CharacterCoordinates, // Assoc, N -> [i] such that characters psi(p_i) determines psi
  Eigenforms, // Assoc, <k, N, chi> -> [ <primes_used, coefficients, p -> T_p(f) > : f in NewformDecomposition ]
  // where Tzeta = is the single generator the Hecke algebra
  // and Tzeta == &+[Tp(f)*c where p := Primes[primes_used[i]]) : i->c in coefficients];
  // and Tp(f) = S*HeckeOperator(M)*S^-1 where _, S, _ := RationalForm(Tzeta)
  filename; // MonStgElt


/*
 * TODO:
 * - convert from magma gen to stored gen
 * - save hecke_gen_*
 */
intrinsic BaseField(C::EigenvaluesCache) -> FldNum
{ return the internal BaseField for the cache structure}
  return C`BaseField;
end intrinsic;


intrinsic Primes(C::EigenvaluesCache) -> SeqEnum[RngOrdIdl]
{ return the current list of primes for the cache structure}
  return C`Primes;
end intrinsic;


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


function IncreasePrimes(C : increase_bound := 100)
  current_bound := C`Primes[#C`Primes];
  new_primes := PrimesUpTo(current_bound + increase_bound, BaseField(C);
  assert Set(new_primes[#C`primes]) eq Set(C`primes);
  C`Primes cat := new_primes[#C`Primes + 1 .. #new_primes];
  return C`Primes;
end funcion;


function IsFaithful(characters, values, indices)
  return #Set(Rows(Transpose(Matrix(Columns(values, indices))))) eq #characters
end function;


intrinsic CharacterCoordinates(C::EigenvaluesCache, psi::GrpHeckeElt) -> SeqEnum[RngIntElt]
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
      primes := IncreasePrimes(C);
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


intrinsic ValuesOnCoordinates(C::EigenvaluesCache, psi::GrpHeckeElt) -> SeqEnum[RngIntElt]
{ return the [Log(psi(p), zeta) : p in Primes(C)[CharacterCoordinates(level, order)]] }
  return [Integers()!'@'(p, psi : Raw := true) : p in primes] where primes := CharacterCoordinates(psi);
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

