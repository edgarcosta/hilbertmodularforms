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
  ClassGroupReps, // an ideal bb for each element of the narrow class group
  PositiveReps, // PositiveReps[bb][t] = nu with trace t
  AllPositiveReps, // AllPositiveReps[bb] = nu with trace at most Precision(M)
  ShintaniReps, // ShintaniReps[bb][t] = nu in Shintani with trace t
  AllShintaniReps, // AllShintaniReps[bb] = nu in Shintani with trace at most Precision(M)
  ReduceIdealToShintaniRep, // ReduceIdealToShintaniRep[bb][I] = nu in Shintani
  IdealElementPairs, // IdealElementPairs[bb] = list of pairs (nn, nu) for nu in Shintani
  MultiplicationTables, // MultiplicationTables[bb] = mult_table where mult_table[nu] = pairs mult to nu
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

intrinsic NarrowClassGroupRepresentatives(M::ModFrmHilD) -> Any
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

intrinsic AllPositiveReps(M::ModFrmHilD) -> Any
  {}
  return M`AllPositiveReps;
end intrinsic;

intrinsic PositiveRepsUpToTrace(M::ModFrmHilD, bb::RngOrdFracIdl, t::RngIntElt) -> SeqEnum
  {}
  reps := [];
  assert t le Precision(M);
  for i := 0 to t do
    reps cat:= PositiveReps(M)[bb][i];
  end for;
  return reps;
end intrinsic;

intrinsic ShintaniReps(M::ModFrmHilD) -> Any
  {}
  return M`ShintaniReps;
end intrinsic;

intrinsic ShintaniRepsUpToTrace(M::ModFrmHilD, bb::RngOrdFracIdl, t::RngIntElt) -> SeqEnum
  {}
  shintani_reps := [];
  assert t le Precision(M);
  for i := 0 to t do
    shintani_reps cat:= ShintaniReps(M)[bb][i];
  end for;
  return shintani_reps;
end intrinsic;

intrinsic AllShintaniReps(M::ModFrmHilD) -> Any
  {}
  return M`AllShintaniReps;
end intrinsic;

intrinsic ReduceIdealToShintaniRep(M::ModFrmHilD) -> Any
  {}
  return M`ReduceIdealToShintaniRep;
end intrinsic;

intrinsic IdealElementPairs(M::ModFrmHilD) -> Any
  {}
  return M`IdealElementPairs;
end intrinsic;

intrinsic MultiplicationTables(M::ModFrmHilD) -> SeqEnum
  {}
  if not assigned M`MultiplicationTables then
    assert HMFEquipWithMultiplication(M);
  end if;
  return M`MultiplicationTables;
end intrinsic;

intrinsic HeckeEigenvalues(M::ModFrmHilD) -> Assoc
  {}
  return M`HeckeEigenvalues;
end intrinsic;

////////// ModFrmHilD creation and multiplication functions //////////

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
  // maybe we should make good choices for narrow class group reps
  // i.e. generators of small trace?
  // TODO: see above 2 lines
  // prec
  M`Precision := prec;
  // zero ideal
  M`ZeroIdeal := ideal<Integers(F)|0>;
  // class group reps
  M`ClassGroupReps := [mp(g) : g in Cl];
  // positive element reps and Shintani reps for each class group rep
  // up to trace bound prec
  M`PositiveReps := AssociativeArray();
  M`AllPositiveReps := AssociativeArray();
  M`ShintaniReps := AssociativeArray();
  M`AllShintaniReps := AssociativeArray();
  M`ReduceIdealToShintaniRep := AssociativeArray();
  M`IdealElementPairs := AssociativeArray();
  for bb in M`ClassGroupReps do
    M`PositiveReps[bb] := AssociativeArray();
    M`ShintaniReps[bb] := AssociativeArray();
    M`ReduceIdealToShintaniRep[bb] := AssociativeArray();
    M`IdealElementPairs[bb] := [];
    for t := 0 to prec do
      M`PositiveReps[bb][t] := PositiveElementsOfTrace(bb, t);
      M`ShintaniReps[bb][t] := ShintaniDomainOfTrace(bb, t);
    end for;
    M`AllPositiveReps[bb] := PositiveRepsUpToTrace(M, bb, prec);
    M`AllShintaniReps[bb] := ShintaniRepsUpToTrace(M, bb, prec);
    for nu in ShintaniRepsUpToTrace(M, bb, prec) do
      M`ReduceIdealToShintaniRep[bb][ideal<Integers(F)|nu>] := nu;
    end for;
    for nu in AllShintaniReps(M)[bb] do
      nn := ShintaniRepesentativeToIdeal(M, bb, nu);
      M`IdealElementPairs[bb] cat:= [[* nn, nu *]];
    end for;
    // now order IdealElementPairs by Norm
  end for;
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

intrinsic HMFEquipWithMultiplication(M::ModFrmHilD) -> ModFrmHilD
  {Assign representatives and a dictionary for it to M.}
  bbs := ClassGroupReps(M);
  positive_reps := PositiveReps(M);
  shintani_reps := ShintaniReps(M);
  ZF := Integers(BaseField(M));
  mult_tables := AssociativeArray();
  for bb in bbs do
    mult_tables[bb] := GetIndexPairs(bb, M);
  end for;
  M`MultiplicationTables := mult_tables;
  return M;
end intrinsic;




////////// Conversion : Shintani elements < = > Ideals ///////////////
/* Converts pairs (bb,nu) <-> (bb,n) based on the set of representatives bb for Cl^+(F)  */

intrinsic IdealToShintaniRepesentative(M::ModFrmHilD, bb::RngOrdIdl, n::RngOrdIdl) -> ModFrmHilDElt
  {Takes a representative [bb] in Cl^+(F) and an integral ideal n in ZF with [n] = [bb^(-1)] and returns Shintani representative (nu) = n*bb}
  ZF := Integers(M);
  _,gen := IsPrincipal(n*bb);
  ShintaniGenerator := ReduceShintaniIdealClass(gen,bb);
  return ShintaniGenerator;
end intrinsic;

intrinsic ShintaniRepesentativeToIdeal(M::ModFrmHilD, bb::RngOrdIdl, nu::RngOrdElt) -> ModFrmHilDElt
  {Takes a representative [bb] in Cl^+(F) and a nu in bb_+ and returns the integral ideal n = bb^(-1)*(nu) in ZF}
  ZF := Integers(M);
  n := bb^(-1)*(nu*ZF);
  return n;
end intrinsic;

