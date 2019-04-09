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
  NarrowClassGroupReps, // SeqEnum[RngOrdElt/RngFracElt]
  Precision, // RngIntElt : trace bound for all expansions with this parent
  ZeroIdeal, // ideal<ZF|0>
  PositiveReps, // PositiveReps[bb] = [nu with trace at most Precision(M)]
  PositiveRepsByTrace, // PositiveReps[bb][t] = [nu with trace t]
  ShintaniReps, // ShintaniReps[bb] = [nu in Shintani with trace at most Precision(M)]
  ShintaniRepsByTrace, // ShintaniReps[bb][t] = [nu in Shintani with trace t]
  ReduceIdealToShintaniRep, // ReduceIdealToShintaniRep[bb][I] = [nu in Shintani]
  IdealElementPairs, // IdealElementPairs[bb][Nm] = list of pairs (nn, nu) for nu in Shintani of Norm Nm
  IdealsByNarrowClassGroup, // IdealElementPairs[bb] = list of all ideal nn with [nn] = [bb]
  AllIdeals, // List of all ideals for all bb ordered by norm
  AllPrimes, // List of all ideals for all bb ordered by norm
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

intrinsic NarrowClassGroupReps(M::ModFrmHilD) -> Any
  {}
  return M`NarrowClassGroupReps;
end intrinsic;

intrinsic Precision(M::ModFrmHilD) -> RngIntElt
  {The Precision of the space M of Hilbert modular forms.}
  return M`Precision;
end intrinsic;

intrinsic ZeroIdeal(M::ModFrmHilD) -> Any
  {}
  return M`ZeroIdeal;
end intrinsic;

intrinsic PositiveReps(M::ModFrmHilD) -> Any
  {}
  return M`PositiveReps;
end intrinsic;

intrinsic PositiveRepsByTrace(M::ModFrmHilD) -> Any
  {}
  return M`PositiveRepsByTrace;
end intrinsic;

intrinsic PositiveRepsUpToTrace(M::ModFrmHilD, bb::RngOrdFracIdl, t::RngIntElt) -> SeqEnum
  {}
  reps := [];
  assert t le Precision(M);
  for i := 0 to t do
    reps cat:= PositiveRepsByTrace(M)[bb][i];
  end for;
  return reps;
end intrinsic;

intrinsic ShintaniReps(M::ModFrmHilD) -> Any
  {}
  return M`ShintaniReps;
end intrinsic;

intrinsic ShintaniRepsByTrace(M::ModFrmHilD) -> Any
  {}
  return M`ShintaniRepsByTrace;
end intrinsic;

intrinsic ShintaniRepsUpToTrace(M::ModFrmHilD, bb::RngOrdFracIdl, t::RngIntElt) -> SeqEnum
  {}
  shintani_reps := [];
  assert t le Precision(M);
  for i := 0 to t do
    shintani_reps cat:= ShintaniRepsByTrace(M)[bb][i];
  end for;
  return shintani_reps;
end intrinsic;

intrinsic ReduceIdealToShintaniRep(M::ModFrmHilD) -> Any
  {}
  return M`ReduceIdealToShintaniRep;
end intrinsic;

intrinsic IdealElementPairs(M::ModFrmHilD) -> Any
  {}
  return M`IdealElementPairs;
end intrinsic;

intrinsic IdealsByNarrowClassGroup(M::ModFrmHilD) -> Any
  {}
  return M`IdealsByNarrowClassGroup;
end intrinsic;

intrinsic AllIdeals(M::ModFrmHilD) -> SeqEnum
  {}
  return M`AllIdeals;
end intrinsic;

intrinsic AllPrimes(M::ModFrmHilD) -> SeqEnum
  {}
  return M`AllPrimes;
end intrinsic;

intrinsic MultiplicationTables(M::ModFrmHilD) -> SeqEnum
  {}
  if not assigned M`MultiplicationTables then
    HMFEquipWithMultiplication(M);
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
  M`NarrowClassGroupReps := [ mp(g) : g in Cl ];
  // maybe we should make good choices for narrow class group reps
  // i.e. generators of small trace?
  // TODO: see above 2 lines
  // prec
  M`Precision := prec;
  // zero ideal
  M`ZeroIdeal := ideal<Integers(F)|0>;
  // positive element reps and Shintani reps for each class group rep
  // up to trace bound prec
  M`PositiveReps := AssociativeArray();
  M`PositiveRepsByTrace := AssociativeArray();
  M`ShintaniReps := AssociativeArray();
  M`ShintaniRepsByTrace := AssociativeArray();
  M`ReduceIdealToShintaniRep := AssociativeArray();
  // Elements and Shintani domains
  for bb in M`NarrowClassGroupReps do
    M`PositiveRepsByTrace[bb] := AssociativeArray();
    M`ShintaniRepsByTrace[bb] := AssociativeArray();
    M`ReduceIdealToShintaniRep[bb] := AssociativeArray();
    for t := 0 to prec do
      M`PositiveRepsByTrace[bb][t] := PositiveElementsOfTrace(bb, t);
      M`ShintaniRepsByTrace[bb][t] := ShintaniDomainOfTrace(bb, t);
    end for;
    M`PositiveReps[bb] := PositiveRepsUpToTrace(M, bb, prec);
    M`ShintaniReps[bb] := ShintaniRepsUpToTrace(M, bb, prec);
    for nu in M`ShintaniReps[bb] do
      M`ReduceIdealToShintaniRep[bb][ideal<Integers(F)|nu>] := nu;
    end for;
  end for;
  // Ideals
  M`IdealsByNarrowClassGroup := AssociativeArray();
  M`IdealElementPairs := AssociativeArray(); 
  for bb in M`NarrowClassGroupReps do
    IdealElementPairsList := [];
    for nu in ShintaniReps(M)[bb] do
      nn := ShintaniRepresentativeToIdeal(bb, nu);
      IdealElementPairsList cat:= [[* nn, nu *]]; //ideals are first
    end for;
    //Sort IdealElementPairs by norm of ideal
    norms := [CorrectNorm(pair[1]) : pair in IdealElementPairsList];
    ParallelSort(~norms, ~IdealElementPairsList);
    M`IdealElementPairs[bb] := IdealElementPairsList;
    M`IdealsByNarrowClassGroup[bb] := [pair[1] : pair in IdealElementPairsList];
  end for;
  // M`Ideals
  all_ideals := &cat[IdealsByNarrowClassGroup(M)[bb] : bb in NarrowClassGroupReps(M)];
  // M`Primes 
  M`AllPrimes := PrimesUpTo(Integers()!Max([CorrectNorm(nn) : nn in all_ideals]), BaseField(M));
  // sort M`Ideals by Norm
  norms := [CorrectNorm(I) : I in all_ideals];
  ParallelSort(~norms, ~all_ideals);
  M`AllIdeals := all_ideals;
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
  bbs := NarrowClassGroupReps(M);
  mult_tables := AssociativeArray();
  for bb in bbs do
    mult_tables[bb] := GetIndexPairs(bb, M);
  end for;
  M`MultiplicationTables := mult_tables;
  return M;
end intrinsic;
