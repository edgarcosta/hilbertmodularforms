/*****
ModFrmHilDGRng
*****/

////////// ModFrmHilDGRng attributes //////////

declare type ModFrmHilDGRng [ModFrmHilD]; // ModFrmHilDGRng contains a ModFrmHilD contains ModFrmHilDElt
declare attributes ModFrmHilDGRng:
  Field, // FldNum : totally real field
  Integers, // RngOrd : ZF
  NarrowClassGroup, // GrpAb
  NarrowClassNumber, // RngIntElt
  NarrowClassGroupMap, // Map : GrpAb -> Set of fractional ideals of ZF
  NarrowClassGroupReps, // SeqEnum[RngIdl]
  UnitGroup, // GrpAb
  UnitGroupMap, // Map : GrpAb -> Units of ZF
  DedekindZetatwo, // FldReElt : Value of zeta_F(2) (Old: Precision needs to be computed relative to weight k)
  places, // SeqEnum : Real places for the field F
  Precision, // RngIntElt : trace bound for all expansions with this parent
  ZeroIdeal, // ideal<ZF|0>
  PositiveReps, // PositiveReps[bb] = [nu with trace at most Precision(M)]
  PositiveRepsByTrace, // PositiveReps[bb][t] = [nu with trace t]
  ShintaniReps, // ShintaniReps[bb] = [nu in Shintani with trace at most Precision(M)]
  ShintaniRepsIdeal, // ShintaniReps[bb] = [ShintaniRepresentativeToIdeal(nu) in Shintani with trace at most Precision(M)]
  ShintaniRepsByTrace, // ShintaniReps[bb][t] = [nu in Shintani with trace t]
  ReduceIdealToShintaniRep, // ReduceIdealToShintaniRep[bb][nn] = nu, such that nu is Shintani reduced
  IdealsByNarrowClassGroup, // IdealElementPairs[bb] = list of all ideal nn with [nn] = [bb]
  AllIdeals, // List of all ideals for all bb ordered by norm
  AllPrimes, // List of all prime ideals for all bb ordered by norm
  MPairs, // Assoc: mapping nu to the sequence
  // [(<s(mu), epsilon>, <s(mu'), epsilon'>) :  mu = epsilon s(mu), mu' = epsilon' s(mu'), mu + mu' = nu],
  // where nu is Shintani reduced, i.e., s(nu) = s(nu')
  // M stands for monoid, multiplication, and mangling
  PrecomputationforTrace, // Precomputed quantities for the Trace formula
  // HMFPrecomputation, // Precomputed quantities for the Trace formula (Old)
  // Book keeping
  // Caching the computation of EigenForms, see Workspace
  // a double indexed Associative Array (level, weight) --> a list of hecke eigenvalues per orbit
  HeckeEigenvalues,
  // a triple indexed Associative Array (level, weight, chi) -> M_k(N, chi)
  Spaces,
  TotallyPositiveUnitGroup, // the group of totally positive units of the base as an abstract group
  TotallyPositiveUnitGroupMap // map from abstract totally positive unit group into R^\times_{>0}
  ;

////////// ModFrmHilDGRng fundamental intrinsics //////////

intrinsic PercentM(M::ModFrmHilDGRng) -> MonStgElt
  {returns a string to produce M in a magma session.}
  return Sprintf("GradedRingOfHMFs(%m, %m)", BaseField(M), Precision(M));
end intrinsic;

intrinsic Print(M::ModFrmHilDGRng, level::MonStgElt)
  {}
  if level in ["Default", "Minimal", "Maximal"] then
    printf "Graded ring of Hilbert modular forms over %o", M`Field;
    printf " with precision %o", M`Precision;
  elif level eq "Magma" then
    printf "%o", PercentM(M);
  else
    error "not a valid printing level.";
  end if;
end intrinsic;

intrinsic 'in'(Mk::., M::ModFrmHilDGRng) -> BoolElt
  {}
  if Type(Mk) ne ModFrmHilD then
    return false, "The first argument should be a ModFrmHilD";
  else
    return Parent(Mk) eq M;
  end if;
end intrinsic;

intrinsic 'eq'(M1::ModFrmHilDGRng, M2::ModFrmHilDGRng) -> BoolElt
  {True iff the two spaces of Hilbert modular forms are identically the same}
  return IsIdentical(M1, M2);
end intrinsic;

////////// ModFrmHilDGRng access to attributes //////////

intrinsic BaseField(M::ModFrmHilDGRng) -> FldAlg
  {The base field of the space M of Hilbert modular forms.}
  return M`Field;
end intrinsic;

intrinsic Integers(M::ModFrmHilDGRng) -> RngOrd
  {}
  return M`Integers;
end intrinsic;

intrinsic NarrowClassGroup(M::ModFrmHilDGRng) -> GrpAb
  {}
  return M`NarrowClassGroup;
end intrinsic;

intrinsic NarrowClassNumber(M::ModFrmHilDGRng) -> RngIntElt
  {}
  return M`NarrowClassNumber;
end intrinsic;

intrinsic NarrowClassGroupMap(M::ModFrmHilDGRng) -> Map
  {}
  return M`NarrowClassGroupMap;
end intrinsic;

intrinsic NarrowClassGroupReps(M::ModFrmHilDGRng) -> Any
  {}
  return M`NarrowClassGroupReps;
end intrinsic;

intrinsic NarrowClassRepresentative(M::ModFrmHilDGRng, I::RngOrdIdl) -> Any
  {Returns the stored NarrowClassGroup representative for I}
  bbs := NarrowClassGroupReps(M);
  mp := NarrowClassGroupMap(M);
  Rep := [bb : bb in bbs | (bb)@@mp eq (I)@@mp]; // Representative for class [ I ]
  return Rep[1];
end intrinsic;

intrinsic UnitGroup(M::ModFrmHilDGRng) -> Any
  {}
  return M`UnitGroup;
end intrinsic;

intrinsic UnitGroupMap(M::ModFrmHilDGRng) -> Any
  {}
  return M`UnitGroupMap;
end intrinsic;

intrinsic TotallyPositiveUnitGroup(M::ModFrmHilDGRng) -> Any
  {}
  return M`TotallyPositiveUnitGroup;
end intrinsic;

intrinsic TotallyPositiveUnitGroupMap(M::ModFrmHilDGRng) -> Any
  {}
  return M`TotallyPositiveUnitGroupMap;
end intrinsic;

intrinsic DedekindZetatwo(M::ModFrmHilDGRng) -> Any
  {}
  if not assigned M`DedekindZetatwo then
    F := BaseField(M); 
    M`DedekindZetatwo := Evaluate(LSeries(F : Precision := 100),2); // Fixed Precision 100. 
  end if;
  return M`DedekindZetatwo;
end intrinsic;

intrinsic places(M::ModFrmHilDGRng) -> Any
  {}
  if not assigned M`places then
    F := BaseField(M);
    M`places := RealPlaces(F);
  end if;
  return M`places;
end intrinsic;

intrinsic Precision(M::ModFrmHilDGRng) -> RngIntElt
  {The Precision of the space M of Hilbert modular forms.}
  return M`Precision;
end intrinsic;

intrinsic ZeroIdeal(M::ModFrmHilDGRng) -> Any
  {}
  return M`ZeroIdeal;
end intrinsic;

intrinsic PositiveReps(M::ModFrmHilDGRng) -> Any
  {}
  return M`PositiveReps;
end intrinsic;

intrinsic PositiveRepsByTrace(M::ModFrmHilDGRng) -> Any
  {}
  return M`PositiveRepsByTrace;
end intrinsic;

intrinsic PositiveRepsUpToTrace(M::ModFrmHilDGRng, bb::RngOrdFracIdl, t::RngIntElt) -> SeqEnum
  {}
  reps := [];
  assert t le Precision(M);
  for i := 0 to t do
    reps cat:= PositiveRepsByTrace(M)[bb][i];
  end for;
  return reps;
end intrinsic;

intrinsic ShintaniReps(M::ModFrmHilDGRng) -> Any
  {}
  return M`ShintaniReps;
end intrinsic;

intrinsic ShintaniRepsByTrace(M::ModFrmHilDGRng) -> Any
  {}
  return M`ShintaniRepsByTrace;
end intrinsic;

intrinsic ShintaniRepsUpToTrace(M::ModFrmHilDGRng, bb::RngOrdFracIdl, t::RngIntElt) -> SeqEnum
  {}
  shintani_reps := [];
  assert t le Precision(M);
  for i := 0 to t do
    shintani_reps cat:= ShintaniRepsByTrace(M)[bb][i];
  end for;
  return shintani_reps;
end intrinsic;

intrinsic ReduceIdealToShintaniRep(M::ModFrmHilDGRng) -> Any
  {}
  return M`ReduceIdealToShintaniRep;
end intrinsic;

intrinsic IdealElementPairs(M::ModFrmHilDGRng) -> Any
  {}
  return M`IdealElementPairs;
end intrinsic;

intrinsic IdealsByNarrowClassGroup(M::ModFrmHilDGRng) -> Any
  {}
  return M`IdealsByNarrowClassGroup;
end intrinsic;

intrinsic AllIdeals(M::ModFrmHilDGRng) -> SeqEnum
  {}
  return M`AllIdeals;
end intrinsic;

intrinsic AllPrimes(M::ModFrmHilDGRng) -> SeqEnum
  {}
  return M`AllPrimes;
end intrinsic;

intrinsic MultiplicationTables(M::ModFrmHilDGRng) -> SeqEnum
  {}
  if not assigned M`MultiplicationTables then
    HMFEquipWithMultiplication(M);
  end if;
  return M`MultiplicationTables;
end intrinsic;

/* Old Code for Trace
intrinsic HMFPrecomputation(M::ModFrmHilDGRng) -> Assoc
  {}
  if not assigned M`HMFPrecomputation then
    HMFTracePrecomputation(M);
  end if;
  return M`HMFPrecomputation;
end intrinsic;
*/

intrinsic TracePrecomputation(M::ModFrmHilDGRng) -> Assoc
  {}
  if not assigned M`PrecomputationforTrace then
    HMFTracePrecomputation(M);
  end if;
  return M`PrecomputationforTrace;
end intrinsic;


intrinsic HeckeEigenvalues(M::ModFrmHilDGRng) -> Assoc
  {}
  return M`HeckeEigenvalues;
end intrinsic;

intrinsic Spaces(M::ModFrmHilDGRng) -> Assoc
  {return the Spaces attribute}
  return M`Spaces;
end intrinsic;

intrinsic AddToSpaces(M::ModFrmHilDGRng, Mk::ModFrmHilD, N::RngOrdIdl, k::SeqEnum[RngIntElt], chi::GrpHeckeElt)
  { adds Mk to the AssociativeArray M`Spaces}
  if not N in Keys(M`Spaces) then
    M`Spaces[N] := AssociativeArray();
  end if;
  M`Spaces[N][<k, chi>] := Mk;
end intrinsic;


////////// ModFrmHilDGRng creation and multiplication functions //////////

intrinsic ModFrmHilDGRngInitialize() -> ModFrmHilD
  {Create an empty ModFrmHilDGRng object.}
  M := New(ModFrmHilDGRng);
  return M;
end intrinsic;

// previously called HMFSpace
intrinsic GradedRingOfHMFs(F::FldNum, prec::RngIntElt) -> ModFrmHilDGRng
  {Generates the space ModFrmHilDGRng over F with level N.}
  assert IsTotallyReal(F);
  M := ModFrmHilDGRngInitialize();
  // field
  M`Field := F;
  R := Integers(F);
  M`Integers := R;
  // narrow class group
  Cl, mp := NarrowClassGroup(F);
  U, mU := UnitGroup(F);
  M`NarrowClassGroup := Cl;
  M`NarrowClassNumber := #Cl;
  M`NarrowClassGroupMap := mp;
  M`NarrowClassGroupReps := [ mp(g) : g in Cl ];
  M`UnitGroup := U;
  M`UnitGroupMap := mU;
  Up, mUp := TotallyPositiveUnits(R);
  M`TotallyPositiveUnitGroup := Up;
  M`TotallyPositiveUnitGroupMap := mUp;
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
  M`ShintaniRepsIdeal := AssociativeArray();
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
    M`ShintaniRepsIdeal[bb] := AssociativeArray();
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
      nn := ShintaniRepresentativeToIdeal(M, bb, nu);
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

  M`Spaces := AssociativeArray();
  return M;
end intrinsic;


intrinsic ModFrmHilDGRngCopy(M::ModFrmHilDGRng) -> ModFrmHilDGRng
  {new instance of ModFrmHilDGRng.}
  M1 := ModFrmHilDGRngInitialize();
  for attr in GetAttributes(Type(M)) do
    if assigned M``attr then
      M1``attr := M``attr;
    end if;
  end for;
  return M1;
end intrinsic;

///////////////////////////////////////////////////
//                                               //
//        Precomputations: Multiplication        //
//                                               //
///////////////////////////////////////////////////

intrinsic HMFEquipWithMultiplication(M::ModFrmHilDGRng)
  {Assign representatives and a dictionary for it to M.}
  bbs := NarrowClassGroupReps(M);
  M`MultiplicationTables := AssociativeArray();
  for bb in bbs do
     // Populates M`MultiplicationTables[bb]
     GetIndexPairs(bb, M);
  end for;
end intrinsic;


///////////////////////////////////////////////////
//                                               //
//         Precomputations: Speed Trace          //
//                                               //
///////////////////////////////////////////////////

/////////////// ModFrmHilD: Trace Precomputation ////////////////

intrinsic HMFTracePrecomputation(M::ModFrmHilDGRng)
  {Fills in the CM-extensions}
  F := BaseField(M); // Base Field
  ZF := Integers(F); // Ring of Integers
  _<x> := PolynomialRing(F); // Polynomial ring over F
  UF := UnitGroup(M); // Unit Group of F
  mUF := UnitGroupMap(M); // Unit Group of F map
  
  // Storage
  AllDiscriminants := []; // Minimal set of discriminants 
  ReducedDiscriminants := []; // Reduced Discriminants
  A := AssociativeArray(); // Storage for precomputations
  

  // First pass. A[a] := List of [b,a,D];
  for mm in IdealsByNarrowClassGroup(M)[1*ZF] do
    A[mm] := [];
    Points := SIndexOfSummation(M,mm);
    for i in Points do
      b := i[1]; // Trace
      a := i[2]; // Norm
      D := b^2-4*a; // Discriminant
      A[mm] cat:= [[* b, a, D*]];
      AllDiscriminants cat:= [D];
    end for;
  end for;


  // Second pass. Compute reduced discriminants, ZK ring of intgers, and conductor ff. 
  CMDisc := Set(AllDiscriminants);
  S := AssociativeArray();
  for D in CMDisc do
    K := ext<F | x^2 - D >; // Field K/F
    ZK := Integers(K); // Ring of Integers 
    DD := Discriminant(ZK); // Discriminant 
    ff := Sqrt((D*ZF)/DD); // Conductor
    D0 := D; // Unique indentifying discriminant
    t := 0; // Counter
    for d in ReducedDiscriminants do 
      if IsSquare(D/d[1]) then 
        t := 1;
        D0 := d[1];
        break;
      end if;
    end for;
    if t eq 0 then  // Add to AllDiscriminants if it is new
      ReducedDiscriminants cat:= [[*D,K*]]; 
    end if;
    S[D] := [*D0, ZK, ff*]; // TODO: storing ring of integers doubles time why?
  end for;


  // Third Pass. Append [D0, ZK, ff] to [b,a,D].
  for mm in IdealsByNarrowClassGroup(M)[1*ZF] do
    A[mm] := [ i cat S[i[3]] : i in A[mm]];
  end for;


  // Fourth pass. Compute class number and unit index [h,w].
  T := AssociativeArray();
  SetClassGroupBounds("GRH"); // No Proof!
  for pair in ReducedDiscriminants do
    D0 := pair[1]; // Indentifying Discriminant
    K := pair[2]; // Field 
    Kabs := AbsoluteField(K); // Class groups computations only for absolute extensions?
    ZKabs := Integers(Kabs); // Ring of integers
    hplus := NarrowClassNumber(M); // Narrow class number
    h,w := ClassGroupandUnitIndex(M, K, D0, ZF, hplus); // Class group of K and Hasse Unit index
    T[D0] := [*h,w*];
  end for;


  // Fifth Pass. Append [h,w] to [b, a, D, D0, ZK, ff].
  for mm in IdealsByNarrowClassGroup(M)[1*ZF] do
    A[mm] := [ i cat T[i[4]] : i in A[mm]];
  end for;
  M`PrecomputationforTrace := A;
end intrinsic;



////////// Trace Precompuation code //////////

/* Old Trace precomputation code
intrinsic HMFTracePrecomputation(M::ModFrmHilDGRng)
  {Fills in the CM-extensions}
  F := BaseField(M);
  ZF := Integers(F);
  _<x> := PolynomialRing(F);

  // Storage
  AllDiscriminants := []; // Minimal set of discriminants 
  A := AssociativeArray(); // Storage for precomputations

  // First pass. A[a] := List of [*b,D*];
  for a in ShintaniReps(M)[1*ZF] do
    Points := CMExtensions(M,a);
    A[a] := [[* b, b^2-4*a *] : b in Points];
    AllDiscriminants cat:= [b^2-4*a : b in Points];
  end for;

  // Second pass. Computing fundamental discriminant and conductor. b^2-4a -> D,f^2
  // Is there a function to take b^2-4a -> Df^2 with D fundamental discriminant?
  CMDisc := Set(AllDiscriminants);
  CMFields := AssociativeArray();
  T := AssociativeArray(); // Keys are CMDisc
  for D in CMDisc do
    K := ext<F | x^2 - D >;
    ZK := Integers(K);
    DD := Discriminant(ZK);
    cc := Sqrt((D*ZF)/DD);
    _,FundD := IsPrincipal(DD); // generator for fundamental discriminant !!! Might be incorrect up to units !!!!
    FundD := -ReduceShintaniMinimizeTrace(TotallyPostiveAssociate(M,FundD)); // Ensure unique totally negative fundamental discriminant.
    T[D] := [*FundD,cc*];
    CMFields[FundD] := K;
  end for;

  // Third pass. Thinning to only fundamental discriminants T[D] := [FundD,cc,h,w];
  SetClassGroupBounds("GRH"); // I'm OK without a proof!
  FundamentalDiscriminants := Keys(CMFields);
  for FundD in FundamentalDiscriminants do
    K := CMFields[FundD];
    L := AbsoluteField(K); // Class groups computations only for absolute extensions?
    h := ClassNumber(L);
    w := #TorsionUnitGroup(L);
    for D in CMDisc do
      if FundD eq T[D][1] then 
        T[D] cat:= [*h,w*];
      end if;
    end for;
  end for;

  //Fourth pass A[a] := List of [*b,D,FundD,cc,h,w*];
  for a in ShintaniReps(M)[1*ZF] do
    A[a] := [ L cat T[L[2]] : L in A[a]];
  end for;
  M`HMFPrecomputation := A;
end intrinsic;
*/


