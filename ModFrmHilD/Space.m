/*****
ModFrmHilD
*****/

////////// ModFrmHilD attributes //////////

declare type ModFrmHilD [ModFrmHilDElt];
declare attributes ModFrmHilD:
  Field, // FldNum : totally real field
  Integers, // RngOrd : ZF
  NarrowClassGroup, // GrpAb
  NarrowClassNumber, // RngIntElt
  NarrowClassGroupMap, // Map : GrpAb -> Set of fractional ideals of ZF
  NarrowClassGroupRepresentatives, // SeqEnum[RngOrdElt/RngFracElt]

  Precision, // RngIntElt : trace bound for all expansions with this parent
  ZeroIdeal, // ideal<ZF|0>
  ClassGroupReps, // an ideal bb for each element of the class group
  // TODO store pairs [nu,nn] where nn = (nu)*bb^-1? to keep track of ideal?
  PositiveReps, // PositiveReps[bb][t] = nu with trace t
  ShintaniReps, // ShintaniReps[bb][t] = nu in Shintani with trace t
  /* Ideals, // SeqEnum[RngOrdIdl] */
  /* Primes, // */
  /* Dictionary, // Assoc maps Ideals[i] to i */
  /* MultiplicationTable, // SeqEnum[pairs of integers] */
  /* Representatives, // SeqEnum[nu] */
  /* DictionaryRepresentatives, // Assoc maps Representatives[i] to i */

  // Book keeping
  // Caching the computation of EigenForms
  HeckeEigenvalues;
  // a dobule indexed Associative Array (level, weight) --> a list of hecke eigenvalues per orbit

////////// ModFrmHilD fundamental intrinsics //////////

intrinsic PercentM(M::ModFrmHilD) -> MonStgElt
  {returns a string to produce M in a magma session.}
  return Sprintf("HMFSpace(%m, %m)", BaseField(M), Precision(M));
end intrinsic;

intrinsic Print(M::ModFrmHilD, level::MonStgElt)
  {}
  if level in ["Default", "Minimal", "Maximal"] then
    printf "Space of Hilbert modular forms over %o.\n", M`Field;
    printf "Precision: %o\n", M`Precision;
  elif level eq "Magma" then
    printf "%o", PercentM(M);
  else
    error "not a valid printing level.";
  end if;
end intrinsic;

intrinsic 'in'(f::., M::ModFrmHilD) -> BoolElt
  {}
  if Type(f) ne ModFrmHilDElt then
    return false, "The first argument should be a ModFrmHilDElt";
  else
    return Parent(f) eq M;
  end if;
end intrinsic;

intrinsic 'eq'(M1::ModFrmHilD, M2::ModFrmHilD) -> BoolElt
  {True iff the two spaces of Hilbert modular forms are identically the same}
  return IsIdentical(M1, M2);
end intrinsic;


////////// ModFrmHilD access to attributes //////////

intrinsic BaseField(M::ModFrmHilD) -> FldAlg
  {The base field of the space M of Hilbert modular forms.}
  return M`Field;
end intrinsic;

intrinsic Integers(M::ModFrmHilD) -> RngOrd
  {}
  return M`Integers;
end intrinsic;

intrinsic NarrowClassGroup(M::ModFrmHilD) -> GrpAb
  {}
  return M`NarrowClassGroup;
end intrinsic;

intrinsic NarrowClassNumber(M::ModFrmHilD) -> RngIntElt
  {}
  return M`NarrowClassNumber;
end intrinsic;

intrinsic NarrowClassGroupMap(M::ModFrmHilD) -> Map
  {}
  return M`NarrowClassGroupMap;
end intrinsic;

intrinsic NarrowClassGroupRepresentatives(M::ModFrmHilD) -> Map
  {}
  return M`NarrowClassGroupRepresentatives;
end intrinsic;

intrinsic Precision(M::ModFrmHilD) -> RngIntElt
  {The Precision of the space M of Hilbert modular forms.}
  return M`Precision;
end intrinsic;

intrinsic ZeroIdeal(M::ModFrmHilD) -> Any
  {}
  return M`ZeroIdeal;
end intrinsic;

intrinsic ClassGroupReps(M::ModFrmHilD) -> Any
  {}
  return M`ClassGroupReps;
end intrinsic;

intrinsic PositiveReps(M::ModFrmHilD) -> Any
  {}
  return M`PositiveReps;
end intrinsic;

intrinsic ShintaniReps(M::ModFrmHilD) -> Any
  {}
  return M`ShintaniReps;
end intrinsic;

/* intrinsic Ideals(M::ModFrmHilD) -> SeqEnum[RngOrdIdl] */
/*   {The Ideals of the space M of Hilbert modular forms.} */
/*   return M`Ideals; */
/* end intrinsic; */

/* intrinsic Primes(M::ModFrmHilD) -> SeqEnum[RngOrdIdl] */
/*   {} */
/*   return M`Primes; */
/* end intrinsic; */

/* intrinsic Dictionary(M::ModFrmHilD) -> Assoc */
/*   {The dictionary for ideals of the space M of Hilbert modular forms.} */
/*   return M`Dictionary; */
/* end intrinsic; */

/* // TODO add text */
/* intrinsic MultiplicationTable(M::ModFrmHilD) -> SeqEnum */
/*   {} */
/*   if not assigned M`MultiplicationTable then */
/*     assert HMFEquipWithMultiplication(M); */
/*   end if; */
/*   return M`MultiplicationTable; */
/* end intrinsic; */

/* // TODO add text */
/* intrinsic DictionaryRepresentatives(M::ModFrmHilD) -> Assoc */
/*   {} */
/*   if not assigned M`DictionaryRepresentatives then */
/*     assert HMFEquipWithMultiplication(M); */
/*   end if; */
/*   return M`DictionaryRepresentatives; */
/* end intrinsic; */

/* // TODO add text */
/* intrinsic Representatives(M::ModFrmHilD) -> SeqEnum */
/*   {} */
/*   if not assigned M`Representatives then */
/*     assert HMFEquipWithMultiplication(M); */
/*   end if; */
/*   return M`Representatives; */
/* end intrinsic; */

intrinsic HeckeEigenvalues(M::ModFrmHilD) -> Assoc
  {}
  return M`HeckeEigenvalues;
end intrinsic;

////////// ModFrmHilD creation functions //////////

intrinsic ModFrmHilDInitialize() -> ModFrmHilD
  {Create an empty ModFrmHilD object.}
  M := New(ModFrmHilD);
  return M;
end intrinsic;

intrinsic HMFSpace(F::FldNum, prec::RngIntElt) -> ModFrmHilD
  {Generates the space ModFrmHilD over F with level N.}
  assert IsTotallyReal(F);
  M := ModFrmHilDInitialize();
  // field
  M`Field := F;
  M`Integers := Integers(F);
  // narrow class group
  Cl, mp := NarrowClassGroup(F);
  M`NarrowClassGroup := Cl;
  M`NarrowClassNumber := #Cl;
  M`NarrowClassGroupMap := mp;
  M`NarrowClassGroupRepresentatives := [ mp(g) : g in Cl ];
  // prec
  M`Precision := prec;
  /* // ideals */
  /* zero_ideal := ideal<Integers(F)|0>; */
  /* Is := [zero_ideal] cat IdealsUpTo(prec, F); */
  /* M`Ideals := Is; */
  /* // primes */
  /* M`Primes := PrimesUpTo(prec, F); */
  /* // dictionary */
  /* dictionary := AssociativeArray(); */
  /* for i := 1 to #Is do */
  /*   dictionary[Is[i]] := i; */
  /* end for; */
  /* M`Dictionary := dictionary; */
  // zero ideal
  M`ZeroIdeal := ideal<Integers(F)|0>;
  // class group reps
  M`ClassGroupReps := [mp(g) : g in Cl];
  // positive element reps and Shintani reps for each class group rep
  // up to trace bound prec
  M`PositiveReps := AssociativeArray();
  M`ShintaniReps := AssociativeArray();
  /* for bb in M`ClassGroupReps do */
  /*   M`PositiveElementReps[bb] := PositiveElementsOfTraceForIdealOfGivenTraceUpTo(bb, prec); */
  /*   M`ShintaniReps[bb] := Shintani_Domain(bb, prec); */
  /* end for; */
  for bb in M`ClassGroupReps do
    M`PositiveReps[bb] := AssociativeArray();
    M`ShintaniReps[bb] := AssociativeArray();
    for t := 0 to prec do
      M`PositiveReps[bb][t] := PositiveElementsOfTrace(bb, t);
      M`ShintaniReps[bb][t] := ShintaniDomainOfTrace(bb, t);
    end for;
  end for;
  // now for each class group rep
  /* for bb in M`ClassGroupReps do */
  /*   dictionary[bb] := AssociativeArray(); */
  /*   nus := PositiveElementsOfTraceForIdealOfGivenTraceUpTo(bb, prec); */
  /*   for i := 1 to #nus do */
  /*     dictionary[bb][nus[i]] := i; */
  /*   end for; */
  /* end for; */
  /* M`Dictionary := dictionary; */
  return M;
end intrinsic;

intrinsic ModFrmHilDCopy(M::ModFrmHilD) -> ModFrmHilD
  {new instance of ModFrmHilD.}
  M1 := ModFrmHilDInitialize();
  for attr in GetAttributes(Type(M)) do
    if assigned M``attr then
      M1``attr := M``attr;
    end if;
  end for;
  return M1;
end intrinsic;

intrinsic GetPosition(M::ModFrmHilD, nu::RngOrdElt) -> RngIntElt
  {returns the position of ideal generated by nu.}
  ZF := Integers(BaseField(M));
  if nu eq ZF!0 then
    return 1;
  end if;
  if assigned M`DictionaryRepresentatives then
    return M`DictionaryRepresentatives[nu];
  else
    assert nu in ZF;
    // I_nu := ideal< ZF | nu >*Different(ZF);
    I_nu := ideal< ZF | nu >;
    assert Norm(I_nu) le Precision(M);
    return Dictionary(M)[I_nu];
  end if;
end intrinsic;

intrinsic GetPosition(M::ModFrmHilD, I::RngOrdIdl) -> RngIntElt
  {returns the position of ideal.}
  return Dictionary(M)[I];
end intrinsic;

intrinsic HMFEquipWithMultiplication(M::ModFrmHilD) -> ModFrmHilD
  {Assign representatives and a dictionary for it to M.}
  class_group_reps := ClassGroupReps(M);
  positive_reps := PositiveReps(M);
  shintani_reps := ShintaniReps(M);
  /* ZF := Integers(BaseField(M)); */
  /* // loop for ideal classes */
  /* indices := GetIndexPairs(M); */
  /* reps := [elt[1] : elt in indices]; */
  /* reps_indexed := [ ZF!0 : i in [1..#reps] ]; */
  /* dict_reps := AssociativeArray(); */
  /* for nu in reps do */
  /*   dict_reps[nu] := GetPosition(M, nu); */
  /* end for; */
  /* mult_table := [[] : nu in reps]; */
  /* for i := 1 to #indices do */
  /*   nu_i := indices[i][1]; */
  /*   pairs_i := indices[i][2]; */
  /*   list_i := [[dict_reps[elt[1]], dict_reps[elt[2]]] : elt in pairs_i]; */
  /*   mult_table[dict_reps[nu_i]] := list_i; */
  /*   reps_indexed[dict_reps[nu_i]] := nu_i; */
  /*   // assert nu_i eq ShintaniGenerator(M, Ideals(M)[i]); */
  /* end for; */
  /* M`Representatives := reps_indexed; */
  /* M`MultiplicationTable := mult_table; */
  /* M`DictionaryRepresentatives := dict_reps; */
  /* return true; */
  return M;
end intrinsic;
