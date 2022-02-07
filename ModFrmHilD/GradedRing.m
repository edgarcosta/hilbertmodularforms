/*****
ModFrmHilDGRng
*****/

////////// ModFrmHilDGRng attributes //////////

declare type ModFrmHilDGRng [ModFrmHilD]; // ModFrmHilDGRng contains a ModFrmHilD contains ModFrmHilDElt
declare attributes ModFrmHilDGRng:
  Field, // FldNum : totally real field
  //FIXME: Move this and everything else that depends on Field only into FldExt
  NarrowClassGroup, // GrpAb
  NarrowClassNumber, // RngIntElt
  NarrowClassGroupMap, // Map : GrpAb -> Set of fractional ideals of ZF
  NarrowClassGroupReps, // SeqEnum[RngOrdIdl] := [bb]
  IdealDualNarrowClassGroupReps, // SeqEnum[RngFracIdl] := [bbp], where bbp := bb*Difference(Integers)^-1]
  NarrowClassGroupRepsToIdealDual, // Assoc, bb -> bbp
  UnitGroup, // GrpAb
  UnitGroupMap, // Map : GrpAb -> Units of ZF
  DedekindZetatwo, // FldReElt : Value of zeta_F(2) (Old: Precision needs to be computed relative to weight k)
  Places, // SeqEnum : Real places for the field F
  Precision, // RngIntElt : trace bound for all expansions with this parent
  ShintaniReps, // ShintaniReps[bb] = [nu in Shintani with trace at most Precision(M)]
  // ShintaniRepsIdeal and IdealShitaniReps cache the conversion nn <-> nu
  // where nn = nu*(bb')^-1 where bb' = dd_F*bb^(-1)
  // note [nn][bb'] = 1
  ShintaniRepsIdeal, // ShintaniReps[bb][nu] := nn
  IdealShitaniReps, // ShintaniReps[bb][nn] :=  nu
  ShintaniRepsByTrace, // ShintaniReps[bb][t] = [nu in Shintani with trace t]
  ReduceIdealToShintaniRep, // ReduceIdealToShintaniRep[bb][nn] = nu, such that nu is Shintani reduced
  IdealsByNarrowClassGroup, // list of all ideals nn with [nn] = [bb]
  Ideals, // List of all ideals for all bb ordered by norm
  IdealsFactored, // a supset of Ideals, where we cache the object so that further Factorization calls are free
  PrimeIdeals, // List of all prime ideals showing as factors of an element of Ideals
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
  // Associative array (k, psi) -> L(psi, 1-k)
  LValues
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
  return Integers(M`Field);
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

intrinsic NarrowClassGroupReps(M::ModFrmHilDGRng) -> SeqEnum[RngOrdIdl]
  {}
  return M`NarrowClassGroupReps;
end intrinsic;

intrinsic IdealDualNarrowClassGroupReps(M::ModFrmHilDGRng) -> SeqEnum[RngFracIdl]
  {}
  return M`IdealDualNarrowClassGroupReps;
end intrinsic;

intrinsic NarrowClassGroupRepsToIdealDual(M::ModFrmHilDGRng) -> Assoc
  {}
  return M`NarrowClassGroupRepsToIdealDual;
end intrinsic;

intrinsic NarrowClassRepresentative(M::ModFrmHilDGRng, I::RngOrdFracIdl) -> RngOrdFracIdl
  {Returns the stored NarrowClassGroup representative for I}
  bbs := NarrowClassGroupReps(M);
  mp := NarrowClassGroupMap(M);
  Rep := [bb : bb in bbs | (bb)@@mp eq (I)@@mp]; // Representative for class [ I ]
  assert #Rep eq 1;
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

intrinsic TotallyPositiveUnits(M::ModFrmHilDGRng) -> GrpAb, Map
  {return the group of totally positive units of the base as an abstract group and the map from abstract totally positive unit group into F^\times_>0}
  return TotallyPositiveUnits(BaseField(M));
end intrinsic;

intrinsic DedekindZetatwo(M::ModFrmHilDGRng) -> Any
  {}
  if not assigned M`DedekindZetatwo then
    F := BaseField(M);
    M`DedekindZetatwo := Evaluate(LSeries(F : Precision := 100),2); // Fixed Precision 100.
  end if;
  return M`DedekindZetatwo;
end intrinsic;

intrinsic Places(M::ModFrmHilDGRng) -> Any
  {}
  if not assigned M`Places then
    F := BaseField(M);
    M`Places := RealPlaces(F);
  end if;
  return M`Places;
end intrinsic;

intrinsic Precision(M::ModFrmHilDGRng) -> RngIntElt
  {The Precision of the space M of Hilbert modular forms.}
  return M`Precision;
end intrinsic;

intrinsic ShintaniReps(M::ModFrmHilDGRng) -> Assoc
  {}
  return M`ShintaniReps;
end intrinsic;

intrinsic ShintaniRepsByTrace(M::ModFrmHilDGRng) -> Assoc
  {}
  return M`ShintaniRepsByTrace;
end intrinsic;

intrinsic ShintaniRepsUpToTrace(M::ModFrmHilDGRng, bb::RngOrdFracIdl, t::RngIntElt) -> SeqEnum
  {}
  shintani_reps := [];
  assert t le Precision(M);
  return &cat[ShintaniRepsByTrace(M)[bb][i] : i in [0..t]];
end intrinsic;

intrinsic ReduceIdealToShintaniRep(M::ModFrmHilDGRng) -> Any
  {}
  return M`ReduceIdealToShintaniRep;
end intrinsic;

intrinsic ShintaniRepsIdeal(M::ModFrmHilDGRng) -> Assoc
  {}
  return M`ShintaniRepsIdeal;
end intrinsic;

intrinsic IdealShitaniReps(M::ModFrmHilDGRng) -> Assoc
  {}
  return M`IdealShitaniReps;
end intrinsic;

intrinsic IdealsByNarrowClassGroup(M::ModFrmHilDGRng) -> Any
  {}
  return M`IdealsByNarrowClassGroup;
end intrinsic;

intrinsic Ideals(M::ModFrmHilDGRng) -> SeqEnum
  {}
  return M`Ideals;
end intrinsic;

intrinsic Factorization(M::ModFrmHilDGRng, nn::RngOrdIdl) -> SeqEnum
  {}
  i := Index(M`IdealsFactored, nn);
  if i gt 0 then
    return Factorization(M`IdealsFactored[i]);
  else
    Include(~M`IdealsFactored, nn);
    return Factorization(nn);
  end if;
end intrinsic;

intrinsic PrimeIdeals(M::ModFrmHilDGRng) -> SeqEnum
  {}
  return M`PrimeIdeals;
end intrinsic;

intrinsic NumberOfCoefficients(M::ModFrmHilDGRng) -> RngIntElt
  {}
  return &+[#elt : elt in ShintaniReps(M)];
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
    M`PrecomputationforTrace := HMFTracePrecomputation(M);
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
  diffinv := Different(R)^-1;
  // narrow class group
  Cl, mp := NarrowClassGroup(F);
  U, mU := UnitGroup(F);
  M`NarrowClassGroup := Cl;
  M`NarrowClassNumber := #Cl;
  M`NarrowClassGroupMap := mp;
  M`NarrowClassGroupReps := [ mp(g) : g in Cl ];
  M`IdealDualNarrowClassGroupReps := [ bb*diffinv : bb in M`NarrowClassGroupReps];
  M`NarrowClassGroupRepsToIdealDual := AssociativeArray();
  for i in [1..#Cl] do
    bb := M`NarrowClassGroupReps[i];
    bbp := M`IdealDualNarrowClassGroupReps[i];
    M`NarrowClassGroupRepsToIdealDual[bb] := bbp;
  end for;
  M`UnitGroup := U;
  M`UnitGroupMap := mU;
  _, _ := TotallyPositiveUnits(F); // it caches it
  // maybe we should make good choices for narrow class group reps
  // i.e. generators of small trace?
  // TODO: see above 2 lines
  // prec
  M`Precision := prec;
  // positive element reps and Shintani reps for each class group rep
  // up to trace bound prec
  M`ShintaniReps := AssociativeArray();
  M`ShintaniRepsIdeal := AssociativeArray();
  M`IdealShitaniReps := AssociativeArray();
  M`ShintaniRepsByTrace := AssociativeArray();
  M`ReduceIdealToShintaniRep := AssociativeArray();
  M`IdealsByNarrowClassGroup := AssociativeArray();
  // Elements and Shintani domains
  // instanciate all associative arrays
  for bb in M`NarrowClassGroupReps do
    M`ShintaniRepsByTrace[bb] := AssociativeArray();
    M`ReduceIdealToShintaniRep[bb] := AssociativeArray();
    M`ShintaniRepsIdeal[bb] := AssociativeArray();
    M`IdealShitaniReps[bb] := AssociativeArray();
  end for;
  for bb in M`NarrowClassGroupReps do
    bbp := M`NarrowClassGroupRepsToIdealDual[bb];
    bbpinv := bbp^-1;
    for t := 0 to prec do
      M`ShintaniRepsByTrace[bb][t] := ShintaniRepsOfTrace(bbp, t);
    end for;
    M`ShintaniReps[bb] := ShintaniRepsUpToTrace(M, bb, prec);
    for nu in M`ShintaniReps[bb] do
      M`ReduceIdealToShintaniRep[bb][ideal<Integers(F)|nu>] := nu;
      nn := NicefyIdeal(nu*bbpinv); // [nn] = [bbpinv] which might differ from [bb]
      M`ShintaniRepsIdeal[bb][nu] := nn;
      M`IdealShitaniReps[bb][nn] := nu;
    end for;
    // the ideals generated in the previous for loop are not in bb class, but in bbpinv's class.
    repbbpinv := NarrowClassRepresentative(M, bbpinv);
    M`IdealsByNarrowClassGroup[repbbpinv] := SetToSequence(Keys(M`IdealShitaniReps[bb]));
    norms := [CorrectNorm(nn) : nn in M`IdealsByNarrowClassGroup[repbbpinv]];
    ParallelSort(~norms, ~M`IdealsByNarrowClassGroup[repbbpinv]);
  end for;

  // M`Ideals
  all_ideals := [0*R] cat &cat[IdealsByNarrowClassGroup(M)[bb][2..#IdealsByNarrowClassGroup(M)[bb]] : bb in NarrowClassGroupReps(M)];
  // sort M`Ideals by Norm
  norms := [CorrectNorm(I) : I in all_ideals];
  ParallelSort(~norms, ~all_ideals);
  M`Ideals := all_ideals;
  M`PrimeIdeals := SetToSequence(SequenceToSet(&cat[[fac[1] : fac in Factorization(nn)] : nn in all_ideals | not IsZero(nn)]));
  // factorization is cached internally
  M`IdealsFactored := SetToIndexedSet(SequenceToSet(all_ideals));
  norms := [CorrectNorm(I) : I in M`PrimeIdeals];
  ParallelSort(~norms, ~M`PrimeIdeals);

  M`Spaces := AssociativeArray();
  M`LValues := AssociativeArray();
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

intrinsic MPairs(M::ModFrmHilDGRng) -> Assoc
  {return MPairs of M}
  if not assigned M`MPairs then
    HMFEquipWithMultiplication(M);
  end if;
  return M`MPairs;
end intrinsic;

intrinsic HMFEquipWithMultiplication(M::ModFrmHilDGRng)
  {Assign representatives and a dictionary for it to M.}
  M`MPairs := AssociativeArray();
  for bb in NarrowClassGroupReps(M) do
    // Populates M`Mpairs[bb]
    ComputeMPairs(bb, M);
  end for;
end intrinsic;


///////////////////////////////////////////////////
//                                               //
//         Precomputations: Speed Trace          //
//                                               //
///////////////////////////////////////////////////

/////////////// ModFrmHilD: Trace Precomputation ////////////////

intrinsic HMFTracePrecomputation(M::ModFrmHilDGRng) -> Assoc
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


  ideals := IdealsByNarrowClassGroup(M)[1*ZF];
  Include(~ideals, 1*ZF); // assure that 1*ZF is always there

  // First pass. A[a] := List of [b,a,D];
  for mm in ideals do
    A[mm] := [];
    Points := SIndexOfSummation(M, mm);
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
  for mm in ideals do
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
  for mm in ideals do
    A[mm] := [ i cat T[i[4]] : i in A[mm]];
  end for;
  return A;
end intrinsic;



////////// Trace Precompuation code //////////

/* Old Trace precomputation code
intrinsic HMFTracePrecomputation(M::ModFrmHilDGRng)
  {Fills in the CM-extensions}
  F := BaseField(M);
  ZF := Integers(F);
  _<x> := PolynomialRing(F);
Ideals
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


