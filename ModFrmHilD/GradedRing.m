/*****
ModFrmHilDGRng
*****/

////////// ModFrmHilDGRng attributes //////////

declare type ModFrmHilDGRng [ModFrmHilD]; // ModFrmHilDGRng contains a ModFrmHilD contains ModFrmHilDElt
declare attributes ModFrmHilDGRng:
  BaseField, // FldNum : totally real field
  //FIXME: Move this and everything else that depends on Field only into FldExt
  NarrowClassGroup, // GrpAb
  NarrowClassNumber, // RngIntElt
  NarrowClassGroupMap, // Map : GrpAb -> Set of fractional ideals of ZF
  NarrowClassGroupRepsMap, // Assoc: g::GrpElt -> bb::RngOrdFracIdl
  NarrowClassGroupReps, // Values(NarrowClassGroupRepsMap)
  IdealDualNarrowClassGroupReps, //  Assoc: g::GrpElt -> bbp::RngOrdFracIdl, where bbp := bb*Difference(Integers)^-1]
  NarrowClassGroupRepsToIdealDual, // Assoc, bb -> bbp
  UnitGroup, // GrpAb
  UnitGroupMap, // Map : GrpAb -> Units of ZF
  DedekindZetatwo, // FldReElt : Value of zeta_F(2) (Old: Precision needs to be computed relative to weight k)
  Places, // SeqEnum : Real places for the field F
  Precision, // RngIntElt : trace bound for all expansions with this parent
  // RepToIdeal and IdealToRep cache the conversion nn <-> nu
  RepToIdeal, // RepToIdeal[bb][nu] := nn
  IdealToRep, // IdealToRep[bb][nn] := nu
  FunDomainReps, // FunDomainReps[bb] stores the list of nu in the bb component 
                 // corresponding to nn of norm at most M`Precision
  FunDomainRepsUpToNorm, // FunDomainRepsUpToNorm[bb][x] stores the list of nu in the bb component 
                         // corresponding to nn of norm at most x
  FunDomainRepsOfNorm, // FunDomainRepsOfNorm[bb][x] stores the list of nu in the bb component
                       // corresponding to nn of norm x
  IdealsByNarrowClassGroup, // list of all ideals nn with [nn] = [bb]
  Ideals, // List of all ideals for all bb ordered by norm
  IdealsFactored, // a supset of Ideals, where we cache the object so that further Factorization calls are free
  PrimeIdeals, // List of all prime ideals showing as factors of an element of Ideals
  MPairs, // Assoc: just for testing, will be replaced soon TODO abhijitm
  Shadows, // Shadows[bb][x] is a SetEnum of <nu, eps> pairs such that the coefficient of nu*eps
           // needs to be included when performing multiplication.
           // Such nu*eps are totally positive elements which are dominated (<= in every real embedding)
           // by some fundamental domain representative.
  PrecomputationforTrace, // Precomputed orders for the Trace formula
  ClassNumbersPrecomputation, // Precomputed class numbers for Trace formula
  // HMFPrecomputation, // Precomputed quantities for the Trace formula (Old)
  // Book keeping
  // Caching the computation of EigenForms, see Workspace
  // a double indexed Associative Array (level, weight) --> a list of hecke eigenvalues per orbit
  HeckeEigenvalues,
  // a triple indexed Associative Array (level, weight, chi) -> M_k(N, chi)
  Spaces,
  // Associative array (k, psi) -> L(psi, 1-k)
  LValues,
  LocalSquares;


 intrinsic IdealRepsMapDeterministic(F::FldNum, mp::Map) -> Assoc
{ Return an associative array where one chooses representatives with minimal label}
  bound := 1;
  Cl := Domain(mp);
  ClElts := [g : g in Cl];
  repsindex := [0 : _ in ClElts];
  while 0 in repsindex do
      ideals := Sort([<StringToInteger(k) : k in Split(l, ".")> cat <elt> where l := LMFDBLabel(elt) : elt in IdealsUpTo(bound, F)]);
      idealsmp := [ elt[3] @@ mp : elt in ideals];
      repsindex := [Index(idealsmp, g) : g in ClElts];
      bound *:= 2;
  end while;
  M := AssociativeArray();
  for i->g in ClElts do
    M[g] := ideals[repsindex[i]][3];
  end for;
  return M;
end intrinsic;


////////// ModFrmHilDGRng fundamental intrinsics //////////

intrinsic PercentM(M::ModFrmHilDGRng) -> MonStgElt
  {returns a string to produce M in a magma session.}
  return Sprintf("GradedRingOfHMFs(%m, %m)", BaseField(M), Precision(M));
end intrinsic;

intrinsic Print(M::ModFrmHilDGRng, level::MonStgElt)
  {}
  if level in ["Default", "Minimal", "Maximal"] then
    printf "Graded ring of Hilbert modular forms over %o", BaseField(M);
    printf " with precision %o", M`Precision;
  elif level eq "Magma" then
      printf "%o", PercentM(M);
  elif level eq "Exosphere" then
      msg := "\n";
      msg *:= "        .-\"\"`\"\"-." * "\n";
      msg *:= "     _/`oOoOoOoOo`\\_" * "\n";
      msg *:= "    '.-= Hilbert =-.'" * "\n";
      msg *:= "    '.-=-=-=-=-=-=-.'" * "\n";
      msg *:= "      `-=.=-.-=.=-'  " * "\n";
      msg *:= "         ^  ^  ^     " * "\n";

      print msg;
      printf "Mothership of Hilbert modular forms over %o", BaseField(M);
      printf " with precision %o\n", M`Precision;
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
  return M`BaseField;
end intrinsic;

intrinsic Integers(M::ModFrmHilDGRng) -> RngOrd
  {}
  return Integers(BaseField(M));
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

intrinsic NarrowClassGroupRepsMap(M::ModFrmHilDGRng) -> Assoc
  {}
  return M`NarrowClassGroupRepsMap;
end intrinsic;

intrinsic NarrowClassGroupRepsToIdealDual(M::ModFrmHilDGRng) -> Assoc
  {}
  return M`NarrowClassGroupRepsToIdealDual;
end intrinsic;

intrinsic NarrowClassRepresentative(M::ModFrmHilDGRng, I::RngOrdFracIdl) -> RngOrdFracIdl
  {Returns the stored NarrowClassGroup representative for I}
  return NarrowClassGroupRepsMap(M)[I @@ NarrowClassGroupMap(M)];
end intrinsic;

intrinsic IdealToNarrowClassRep(M::ModFrmHilDGRng, nn::RngOrdIdl) -> RngOrdIdl
    {
      Given an integral ideal nn, returns the narrow class bb representing
      the component on which the corresponding nu lives. 
    }
    
    require not IsZero(nn) : "The zero ideal lives on every component.";
    dd := Different(Integers(M));

    // nn should be in the class of bbp^-1 = bb^-1 * dd,
    // so the class of the bb corresponding to nn
    // is that of nn^-1 * dd
    bb_class := (nn^-1 * dd) @@ M`NarrowClassGroupMap;
    return M`NarrowClassGroupRepsMap[bb_class];
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
  return &+[#elt : bb->elt in FunDomainReps(M)];
end intrinsic;

intrinsic TracePrecomputation(M::ModFrmHilDGRng) -> Assoc
  {}
  return M`PrecomputationforTrace;
end intrinsic;

intrinsic TracePrecomputationByIdeal(M::ModFrmHilDGRng, mm::RngOrdIdl) -> Assoc
  {}
  if not IsDefined(TracePrecomputation(M),mm) then
    HMFTracePrecomputation(M,[mm]);
    vprintf HilbertModularForms, 1 :
      "running precomputation for ideal %o. \n", IdealOneLine(mm);
  end if;
  return TracePrecomputation(M)[mm];
end intrinsic;


intrinsic ClassNumbersPrecomputation(M::ModFrmHilDGRng) -> Assoc
  {}
  return M`ClassNumbersPrecomputation;
end intrinsic;


intrinsic HeckeEigenvalues(M::ModFrmHilDGRng) -> Assoc
  {}
  return M`HeckeEigenvalues;
end intrinsic;

intrinsic Spaces(M::ModFrmHilDGRng) -> Assoc
  {return the Spaces attribute}
  return M`Spaces;
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
  M`BaseField := F;
  R := Integers(F);
  diffinv := Different(R)^-1;
  // narrow class group
  Cl, mp := NarrowClassGroup(F);
  U, mU := UnitGroup(F);
  M`NarrowClassGroup := Cl;
  M`NarrowClassNumber := #Cl;
  M`NarrowClassGroupMap := mp;



  // Deterministically finding representatives for Cl
  M`NarrowClassGroupRepsMap, _ := IdealRepsMapDeterministic(F, mp);
  M`NarrowClassGroupReps := [M`NarrowClassGroupRepsMap[g] : g in Cl];
  M`IdealDualNarrowClassGroupReps := [ bb*diffinv : bb in M`NarrowClassGroupReps];
  M`NarrowClassGroupRepsToIdealDual := AssociativeArray();
  for i->bb in M`NarrowClassGroupReps do
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

  // This function sets the M`RepToIdeal and M`IdealToRep assocs.
  M`RepToIdeal, M`IdealToRep := RepIdealConversion(M);

  // The associative arrays FunDomainIdlReps and
  // FunDomainEltReps are keyed by narrow class group 
  // This function sets the M`FunDomainRepsUpToNorm assocs.
  //
  // The associative array FunDomainRepsUpToNorm is keyed by narrow class group 
  // representatives bb (these are integral ideals)
  // and nonnegative integers up to prec with values 
  // FunDomainRepsUpToNorm[bb][x]. 
  //
  // The elements of FunDomainReps[bb][x] are the nu corresponding
  // to integral ideals nn with norm up to x lying in the narrow class
  // of [bbp]^-1, i.e. such that nn * bbp = (nu) for some 
  // integral ideal nn of norm up to x.
  PopulateFunDomainRepsArrays(M);

  M`FunDomainReps := AssociativeArray();
  for bb in M`NarrowClassGroupReps do
    M`FunDomainReps[bb] := M`FunDomainRepsUpToNorm[bb][M`Precision];
  end for;

  M`IdealsByNarrowClassGroup := AssociativeArray();
  M`PrecomputationforTrace := AssociativeArray();
  M`ClassNumbersPrecomputation := AssociativeArray();
  // instanciate all associative arrays
  for bb in M`NarrowClassGroupReps do
    bbp := M`NarrowClassGroupRepsToIdealDual[bb];
    bbpinv := bbp^-1;
    // the ideals generated in the previous for loop are not in bb class, but in bbpinv's class.
    repbbpinv := NarrowClassRepresentative(M, bbpinv);
    M`IdealsByNarrowClassGroup[repbbpinv] := SetToSequence(Keys(M`IdealToRep[bb]));
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
    M`MPairs[bb] := ComputeMPairs(M, bb);
  end for;
end intrinsic;


///////////////////////////////////////////////////
//                                               //
//         Precomputations: Trace                //
//                                               //
///////////////////////////////////////////////////

/////////////// ModFrmHilD: Trace Precomputation ////////////////

// FIXME: HMFTracePrecomputation - Pass tracebasis to IdealCMextensions instead of computing each time

intrinsic HMFTracePrecomputation(M::ModFrmHilDGRng, L::SeqEnum[RngOrdIdl])
  {Precomputes class number and unit indices for a list of ideals L}

  // initialize
  F := BaseField(M); // Base Field
  ZF := Integers(F); // Ring of Integers
  _<x> := PolynomialRing(F); // Polynomial ring over F
  UF := UnitGroup(M); // Unit Group of F
  mUF := UnitGroupMap(M); // Unit Group of F map
  C,mC := ClassGroup(F); // class group
  Creps := [ mC(i) : i in C ]; // class group representatives
  NCreps := NarrowClassGroupReps(M); // narrow class group representatives
  SetClassGroupBounds("GRH"); // Bounds

  /////////// Hash function //////////
  // For each discriminant d, this hash function associates a unique element w in F representing the field F(x)/(x^2-d) up to isomorphism over QQ. It runs in two phases:
  //
  // *  Phase 1: Pick a unique representative for the square class of [d] in F*/F*2. Write the discriminant as d * ZF = mm * aa^2 with mm squarefree. Fix a set of representatives for the class group,
  //             and let bb = [ aa ] be the ideal representing the class of aa in CL(F). Then [aa * bb^(-1)] = (x) for some x in ZF so d * ZF = mm * bb^2 * (x)^2. Let d0 := d / x^2. 
  //             Thus a unique representative for the square class of d can be picked as the "reduced fundamental domain rep generator" for -d0 with respect the square of the fundamental unit.
  // 
  // *  Phase 2: Let s : F -> F be the nontrivial automorphism of the quadratic field F. The fields F[x]/(x^2 - d) and F/(x^2 - s(d)) are isomorphic over QQ. We pick a unique 
  //             representative w by selecting either d0 or s(d0) based on which one has the larger embedding in the first real place. We record whether we took d0 or s(d0) 
  //             using an indicator function c, where (c = 0) <=> d0 and (c = 1) <=> s(d0). 
  //              

  function DiscriminantHash(d)
    // Phase 1
    mm := d * ZF;
    aa := &*( [1*ZF] cat [ pp[1] ^ (pp[2] div 2) : pp in Factorization(mm)] ); // Note pp[2] div 2 = Floor(pp[2]/2)
    for bb in Creps do
      boo, x := IsPrincipal( aa * bb^(-1) );
      if boo then
        elt := FunDomainRep( -d / x^2 : lattice := "squares");
        D := ZF ! -elt;
        break;
      end if;
    end for;
    // assert IsSquare(D/d); // can be dropped 
    // Phase 2
    c := 0; // keeps track of conjugation 0 = no conjugation, 1 = conjugation
    E := RealEmbeddings(D);
    if E[1] lt E[2] then
      D := Conjugate(D);
      c := 1;
    end if;
    return D, c;
  end function;


  // Precomputations
  A := TracePrecomputation(M);
  B := ClassNumbersPrecomputation(M);

  // First pass. A[mm][aa] := List of [b,a,D]
  vprintf HilbertModularForms, 1 : "start %o. \n", Cputime();

  Discs := {};
  ideals := Set(L) diff Keys(A); // ideals to precompute
  for mm in ideals do
    A[mm] := AssociativeArray();
    for aa in Creps do
      A[mm][aa] := [];
      if IsNarrowlyPrincipal(mm * aa^2) then
        Points := IndexOfSummation(M, mm, aa : precomp := true);
        for i in Points do
          b := i[1]; // Trace
          a := i[2]; // Norm
          D := b^2-4*a; // Discriminant
          A[mm][aa] cat:= [[b,a,D]];
          Include(~Discs, D);
        end for;
      end if;
    end for;
  end for;


  // Second pass. Compute a hash with unique discriminants up to squares.
  vprintf HilbertModularForms, 1 : "Pass 1 finished at %o. Now computing reduced discriminants for %o orders. \n", Cputime(), #Discs;

  Hash := AssociativeArray();
  RDiscs := {};
  for D in Discs do
    d, c := DiscriminantHash(D);
    Include(~RDiscs, d);
    Hash[D] := [d, c];
  end for;


  // Third pass. Compute ring of integers, class numbers, and unit index for new keys
  NK := RDiscs diff Keys(B);
  vprintf HilbertModularForms, 1 : "Pass 2 finished at %o. Now computing class numbers and unit indices for %o fields. \n", Cputime(), #NK;

  for D in NK do
    K := ext<F | x^2 - D >; // Field K/F
    ZK := Integers(K); // Ring of Integers
    DD := Discriminant(ZK); // Discriminant
    hplus := NarrowClassNumber(M); // Narrow class number
    h,w := ClassNumberandUnitIndex(M, K, D, ZF, hplus); // Class group of K and Hasse Unit index
    B[D] := [* h, w, DD *];
  end for;


  // Fourth Pass. Removing pairs where ff/aa is not integral 
  vprintf HilbertModularForms, 1 : "Pass 3 finished at %o. Now removing pairs where ff/aa is not integral. \n", Cputime();
  
  for mm in ideals do
    for aa in Creps do
      L := [];
      for i in A[mm][aa] do 
        D := i[3];
        d,c := Explode( Hash[D] );
        DD := (c eq 0) select B[d][3] else Conjugate( B[d][3] ); // Discriminant
        ff := ideal < ZF | D*ZF * DD^(-1) >; // Conductor (squared)
        // remove pairs where ff/aa is not integral
        if ff subset aa^2 then
          L cat:= [ [i[1], i[2], d, c] ];
        end if;
      end for;
      A[mm][aa] := L;
    end for;
  end for;

  // verbose printing
  vprintf HilbertModularForms, 1 : "Pass 4 finished at %o. \n", Cputime();

  // Assign
  M`PrecomputationforTrace := A;
  M`ClassNumbersPrecomputation := B;

end intrinsic;



/* Caching Local Squares
// Computing Artin symbols is the 3rd most expensive computation for the trace code (after class numbers and unit indices). 
To compute the Artin symbol (K/pp) for the extension K = F[x] / (x^2 - D) and a prime pp, we need to
  (1) Compute the ring of integers ZK and check if pp | disc(ZK) => return 0
  (2) Check if D is a local square in the completion F_pp => return 1, else -1
Since the local square computation is performed many times, we store the results to M to avoid repeating computations */
intrinsic LocalSquare(M::ModFrmHilDGRng, d::RngOrdElt, pp::RngOrdIdl) -> RngIntElt
  {Checks if D is a local square in the completion F_pp}

  // initialize - LocalSquares
  if not assigned M`LocalSquares then 
    M`LocalSquares := AssociativeArray();
  end if;

  // initialize - LocalSquares[pp]
  if not IsDefined(M`LocalSquares,pp) then
    M`LocalSquares[pp] := AssociativeArray();
  end if;

  // initialize - LocalSquares[pp][d] 
  if not IsDefined(M`LocalSquares[pp],d) then
    M`LocalSquares[pp][d] := IsLocalSquare(d,pp) select 1 else -1; 
  end if;

  return M`LocalSquares[pp][d];
end intrinsic;




/////////////// ModFrmHilD: Precompuations for trace forms ////////////////


intrinsic PrecomputeTraceForm(M::ModFrmHilDGRng)
  { Precomputes values to generate traceforms tr }
  HMFTracePrecomputation(M, Ideals(M));
end intrinsic;


intrinsic PrecomputeTraceForms(M::ModFrmHilDGRng, L::SeqEnum[RngOrdIdl])
  {Given a list of ideals L = [aa,bb, ...], precomputes values to generate traceforms t_aa, t_bb, ... }
  A := SetToSequence({ ii * aa : ii in Ideals(M), aa in L }); // Set of ideals
  HMFTracePrecomputation(M,A);
end intrinsic;

//////////////// Enumeration of Totally Positive Elements ////////////////

intrinsic ElementsInABox(M::ModFrmHilDGRng, aa::RngOrdFracIdl,
                         XLBound::Any, YLBound::Any, XUBound::Any, YUBound::Any) -> SeqEnum
  {Enumerates all elements c in aa with XLBound <= c_1 <= XUBound and  YLBound <= c_2 <= YUBound}

  for bnd in [XUBound, YUBound, XLBound, YLBound] do
    require ISA(Type(bnd),FldReElt) : "Bounds must be coercible to real numbers";
  end for;
  basis := TraceBasis(aa);
  F := BaseField(M);
  ZF := Integers(M);
  places := Places(M);

  //if Evaluate(basis[2],places[1]) lt 0 then
  //  basis := [basis[1], -basis[2]];
  //end if;


  // Precomputationss
  a_1 := Evaluate(basis[1], places[1]);
  a_2 := Evaluate(basis[1], places[2]);
  b_1 := Evaluate(basis[2], places[1]);
  b_2 := Evaluate(basis[2], places[2]);
  assert b_1 lt 0 and b_2 gt 0; // if this assumption changes, the inequalities get swapped

  // List of all Elements
  T := [];
  trLBound := Ceiling(XLBound+YLBound);
  trUBound := Floor(XUBound+YUBound);
  for i in [trLBound..trUBound] do
    // at place 1, i*a2 + j*b2 <= XUBound => j >= (XUBound -i*a1)/b1
    // at place 2, i*a2 + j*b2 >= YLBound => j >= (YLBound -i*a2)/b2
    lBound := Ceiling(Max((XUBound-i*a_1)/b_1, (YLBound-i*a_2)/b_2));
    uBound := Floor(Min((XLBound-i*a_1)/b_1, (YUBound-i*a_2)/b_2));
    for j in [lBound..uBound] do
      Append(~T, i*basis[1] + j*basis[2]);
    end for;
  end for;

  return T;
end intrinsic;

// Rearranges the basis for an ideal so that the second basis vector has trace 0
intrinsic TraceBasis(aa::RngOrdFracIdl) -> SeqEnum
  {Given a fractional ideal aa, returns a basis (a,b) in Smith normal form
   where Trace(a) = n > 0 and Trace(b) = 0}

  // Preliminaries
  B := Basis(aa);
  ZF := Parent(B[2]);
  places := InfinitePlaces(NumberField(ZF));

  // Change of basis
  trMat := Matrix([[Integers()!Trace(B[i])] : i in [1..#B]]);
  _, Q := HermiteForm(trMat);
  B := Eltseq(Vector(B)*Transpose(ChangeRing(Q,ZF)));
  assert Trace(B[1]) gt 0;
  assert Trace(B[2]) eq 0;
  // Orienting B
  if Evaluate(B[2], places[2]) lt 0 then
    B := [B[1], -B[2]];
  end if;
  return B;
end intrinsic;
