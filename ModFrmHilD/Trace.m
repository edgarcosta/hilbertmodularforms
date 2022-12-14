
///////////////////////////////////////////////////
//                                               //
//                 Trace Formula                 //
//                                               //
///////////////////////////////////////////////////

/*
Trace (Main function): Computes Tr T(mm) on an HMFspace Mk
  * TraceProduct (Subroutine): Computes trace of T(mm) * P(aa) on the full space with all characters.
  * PrecompTraceProduct (Subroutine): Computes trace of T(mm) * P(aa) on the full space with all characters using precomputations.

TODOS
* Bad primes - Our "Hecke Operator" is not the true Hecke Operator at bad primes.
* Correction factor for spaces with k = (2,..,2) and chi = 1
* Test nonparallel weight and odd degree weight.
* Cubic fields.

FIXME
* Large weight is off
* Class group + class group representatives should be stored GradedRing.m
* Check that we want to use chi^(-1) instead of chi in the computation for Trace
* Test characters with nontrivial infite part of the modulus, i.e. Q(sqrt60) with weight [4,4]

Notes
* Computing unit index and class groups. The big bottleneck is precomputing the
class numbers #CL(K) and Hasse unit index [ZK^* : ZF^*] for lots of CM-extensions K/F.
I have some code to quickly compute the Hasse unit index without doing the class group.

 */

///////////////////////////////// ModFrmHilD: Trace //////////////////////////////////////////////
//
declare verbose HMFTrace, 3;

intrinsic Trace(Mk::ModFrmHilD, mm::RngOrdIdl : precomp := false) -> RngElt
  {Finds the trace of Hecke Operator T(mm) on Mk}
  // This is wrong at 1*Zf and k = 2, see CuspDimension for the fix

  // Initialize
  k := Weight(Mk);
  F := BaseField(Mk);
  ZF := Integers(F);
  C,mC := ClassGroup(F);
  CReps := [ mC(i) : i in C ];
  chi := Character(Mk)^(-1);
  m,p := Conductor(chi);
  ZK := Parent(chi)`TargetRing; // Coefficient ring for the range of the Hecke Character

  // requirements
  require m eq 1*ZF: "Only supports characters on the narrow class group";
  if #p ne 0 then print "Warning : Narrow ray class groups have not been tested yet"; end if;
  require #Set(k) eq 1: "Not implemented for nonparallel weights";

  // Compute Trace[ T(mm) * P(aa) ] over representatives aa for the class group
  if precomp then
    return (1/#C) * &+[ 1 / Norm(aa) ^ (k[1]-2) * chi(aa) * (ZK ! PrecompTraceProduct(Mk,mm,aa)) : aa in CReps ];
  else
    return (1/#C) * &+[ 1 / Norm(aa) ^ (k[1]-2) * chi(aa) * (ZK ! TraceProduct(Mk,mm,aa)) : aa in CReps ];
  end if;
end intrinsic;



///////////////////////////////// ModFrmHilD: TraceProduct ////////////////////////////////////////////

function WeightFactor(u, t, prec)
  // \sum D_k T^k = 1/(T^2 + T*t + u)^2
  // returns \sum_{k <= prec} Norm(D_{k-2}) T^{k}
  res := [1/u, -t/u^2] cat [Parent(t) | 0 : _ in [0..prec-2 + 1]];
  rm2 := res[1];
  rm1 := res[2];
  for k in [3..prec-1] do
    rm2, rm1 := Explode([rm1, -(t*rm1 + u*rm2)]);
    res[k] := rm1;
  end for;
  R<T> := PowerSeriesRing(Rationals());
  return T^2*R![i mod 2 eq 1 select Norm(elt) else 0: i->elt in res] + O(T^(prec + 1));
end function;



// Artin Symbol
function ArtinSymbol(pp, ZK)
  if IsSplit(pp, ZK) then
    return 1;
  elif IsRamified(pp, ZK) then
    return 0;
  else
    return -1;
  end if;
end function;


function ConductorSum(ZF, NN, aa, u, t, ZK, ff)
  // F is the base field of HMFs
  // NN level
  // aa ideal for the diamond operator
  // ff is the conductor associated to the pair (u, t) = x^2 - t*x + u
  //
  //
  // conductorsum := Sum_{bb | f}  A_bb * B_bb // Sum over suborders S_bb containing S_ff with conductors bb
  // A_bb := Norm(bb) * prod_{pp | bb} ( 1-  ArtinSymbol( K | pp ) Norm(pp) )  -- Term for converting class number h(S_bb) to class number of  maximal order h_k.
  // B_bb :=  Embedding numbers for the order S_bb
  conductorsum := 0;
  for bb in Divisors( ideal< ZF | ff * aa^(-1) > ) do
    // term from converting class number of order to class number of maximal order
    term := Norm(bb) * (&*([1] cat [1 - ArtinSymbol(pp[1], ZK) * Norm(pp[1])^(-1) : pp in Factorization(bb)]));
    // Embedding numbers
    for pp in Factorization(NN) do
      // Create a polynomial x^2 + b1x + a1 with conductor bb
      t0, u0 := PolynomialMaximalOrder(t, u, ZF, pp[1]);
      pi := UniformizingElement(pp[1]);
      vbb := Valuation(bb, pp[1]);
      t1 := t0 * pi^(vbb);
      u1 := u0 * pi^(2 * vbb);
      term *:= EmbeddingNumbers(t1, u1, pp[1], pp[2]);
    end for;
    conductorsum +:= term;
  end for;
  return conductorsum;
end function;

function ClassNumberOverUnitIndex(K, UF, mUF)
  // K CM quadratic extension of F
  // UF unit group of F
  // mUF the map from the group to F
  Kabs := AbsoluteField(K);
  ZKabs := Integers(Kabs);
  UK, mUK := UnitGroup(ZKabs);
  _, mKabstoK := IsIsomorphic(Kabs,K);
  hK := ClassNumber(Kabs); // h = Class number
  // Unit index w = 2 * [ZK : ZF]
  UnitIndex := 2 * #quo< UK | [ (mKabstoK(mUF(u)))@@mUK : u in Generators(UF) ] >;
  return hK / UnitIndex;
end function;

intrinsic HilberSeriesCuspSpace(M::ModFrmHilDGRng, NN::RngOrdIdl) -> RngSerPowElt
  { Ben will write this }

  R<T> := PowerSeriesRing(Rationals());
  F := BaseField(M);
  ZF := Integers(F);
  _<x> := PolynomialRing(ZF);
  n := Degree(F);
  Disc := Discriminant(ZF);
  h := ClassNumber(F);
  UF, mUF := UnitGroup(ZF);

  // for consistency with the rest of the code for trace formulas
  mm := 1*ZF; // hecke operator
  aa := 1*ZF; // diamond operator

  // list of pairs (u,t) that we will sum over
  // FIXME maybe do (u,t) and (u,-t) in one go
  pairs := IndexOfSummation(M, mm, aa);

  // FIXME something is off
  degree := 2 + (4*n - 1) + 2*#pairs;
  prec := 8*degree;

  // Correction term for weight 2
  res := (-1)^(n+1) * NarrowClassNumber(M)*T^2;

  // Constant term
  B := h * Norm(NN) * Abs(DedekindZetaExact(F,-1)) / 2^(n-1);
  B *:= &*( [1] cat [1 + Norm(p[1])^(-1) : p in Factorization(NN)] );

  res +:= B*R!([(k mod 2 eq 0 and k gt 0) select (k-1)^(n) else 0 : k in [0..prec]]);
  res +:= O(T^(prec + 1));


  for pair in pairs do
  //for pair in IndexOfSummation(M, mm, aa) do
    t, u := Explode(pair);
    D := t^2 - 4*u;
    // Requirements
    require IsTotallyPositive(-D): "Non CM-extension in summation";
    K := ext<F | x^2 - D >;
    ZK := Integers(K);
    DD := Discriminant(ZK);
    ff := Sqrt((D*ZF)/DD); // Conductor

    vprintf HMFTrace : "ClassNumberOverUnitIndex: <%o, %o> %o\n", u, t, ClassNumberOverUnitIndex(K, UF, mUF);
    vprintf HMFTrace : "ConductorSum: <%o, %o> %o\n", u, t, ConductorSum(ZF, NN, aa, u, t, ZK, ff);
    // C(u,t)
    C := ClassNumberOverUnitIndex(K, UF, mUF) * ConductorSum(ZF, NN, aa, u, t, ZK, ff);
    vprintf HMFTrace : "WeightFactor: <%o, %o> %o\n", u, t, WeightFactor(u, t, prec);
    res +:= C*WeightFactor(u, t, prec);
  end for;
  R<X> := PolynomialRing(Rationals());
  b, num, den := RationalReconstruction(R!AbsEltseq(res), X^(prec + 1), prec div 2, prec div 2);
  assert b;
  return num/den;
end intrinsic;


intrinsic TraceProduct(Mk::ModFrmHilD, mm::RngOrdIdl, aa::RngOrdIdl) -> RngElt
  {Computes Trace[ T(mm) * P(aa) ] where T(mm) is the mth hecke operator and P(aa) is the diamond operator}

  // If mm * aa^2 = 0 or is not narrowly principal then return 0
  mmaa := mm * aa^2;
  if IsZero(mmaa) or not IsNarrowlyPrincipal(mmaa) then
    return 0;
  end if;

  // Preliminaries
  M := Parent(Mk);
  NN := Level(Mk);
  k := Weight(Mk);
  F := BaseField(Mk);
  ZF := Integers(Mk);
  n := Degree(F);
  places := Places(M);
  _<x> := PolynomialRing(ZF);
  UF, mUF := UnitGroup(ZF);
  Indexforsum := IndexOfSummation(M, mm, aa);

  // Set class group bound for faster computations
  SetClassGroupBounds("GRH");

  // Summation
  Sumterm := 0;
  for pair in Indexforsum do

    // Preliminaries
    b := pair[1];
    a := pair[2];
    D := b^2-4*a;
    K := ext<F | x^2 - D >;
    ZK := Integers(K);
    DD := Discriminant(ZK);
    ff := Sqrt((D*ZF)/DD); // Conductor
    Kabs := AbsoluteField(K);
    ZKabs := Integers(Kabs);
    UK,mUK := UnitGroup(ZKabs);
    _, mKabstoK := IsIsomorphic(Kabs,K);
    h := ClassNumber(Kabs); // h = Class number

    // Unit index w = 2 * [ZK : ZF]
    w := 2 * #quo< UK | [ (mKabstoK(mUF(u)))@@mUK : u in Generators(UF) ] >;
    vprintf HMFTrace : "ClassNumberOverUnitIndex: <%o, %o> %o\n", a, b, h/w;

    // Requirements
    require IsTotallyPositive(-D): "Non CM-extension in summation";

    ///////////////////  Helper Functions //////////////////////

    // Weightfactor
    Weightfactor := function(b,a,l)
      _<x> := PowerSeriesRing(RealField(k[1]+20),k[1]+20); // extend with weight
      P := 1/(1 + b*x + a*x^2);
      return Coefficient(P,l);
    end function;

    // Artin Symbol
    function ArtinSymbol(pp)
      if IsSplit(pp,ZK) then return 1;
      elif IsRamified(pp,ZK) then return 0;
      else return -1; end if;
    end function;

    /////////////////// Conductor sum //////////////////////

    // Constant — FIXME: Remove Round? (see Weightfactor)
    C := (h/w) * Round( &*[ Weightfactor( Evaluate(b,places[i]), Evaluate(a,places[i]), k[i]-2 ) : i in [1..n]] );

    // Conductor Sum
    conductorsum := 0;
    for bb in Divisors( ideal< ZF | ff * aa^(-1) > ) do
      // term from converting class number of order to class number of maximal order
      term := Norm(bb) * (&*([1] cat [1 - ArtinSymbol(pp[1]) * Norm(pp[1])^(-1) : pp in Factorization(bb)]));
      // Embedding numbers
      for pp in Factorization(NN) do
        // Create a polynomial x^2 + b1x + a1 with conductor bb
        b0, a0 := PolynomialMaximalOrder(b,a,ZF,pp[1]);
        pi := UniformizingElement(pp[1]);
        vbb := Valuation(bb,pp[1]);
        b1 := b0 * pi^(vbb);
        a1 := a0 * pi^(2 * vbb);
        term *:= EmbeddingNumbers(b1,a1,pp[1],pp[2]);
      end for;
      conductorsum +:= term;
    end for;
    vprintf HMFTrace : "ConductorSum: <%o, %o> %o\n", a, b, conductorsum;
    vprintf HMFTrace : "WeightFactor: <%o, %o> %o\n", a, b, Round(&*[ Weightfactor( Evaluate(b,places[i]), Evaluate(a,places[i]), k[i]-2 ) : i in [1..n]]);
    vprintf HMFTrace : "%o\n", &*["#" : _ in [1..30]];

    // Add to Sumterm
    Sumterm +:= C * conductorsum;
  end for;

  // Trace is Constant term + Sum term
  tr := ConstantTerm(Mk,mmaa) + Sumterm;
  return tr;
end intrinsic;






/////////////////////////////// ModFrmHilD: PrecompTraceProduct /////////////////////////////////////////

intrinsic PrecompTraceProduct(Mk::ModFrmHilD, mm::RngOrdIdl, aa::RngOrdIdl) -> RngElt
  {Computes trace of T(mm) * P(aa) for Hecke operator T(mm) and Diamond operator P(aa) using precomputations.}

  // If mm * aa^2 = 0 or is not narrowly principal then return 0
  mmaa := mm * aa^2;
  if IsZero(mmaa) or not IsNarrowlyPrincipal(mmaa) then
    return 0;
  end if;

  // Space Preliminaries
  M := Parent(Mk);
  NN := Level(Mk);
  NNfact := Factorization(NN);
  k := Weight(Mk);
  F := BaseField(Mk);
  ZF := Integers(Mk);
  n := Degree(F);
  places := Places(M);
  _<x> := PolynomialRing(ZF);

  // Check precomputations
  if not IsDefined( TracePrecomputation(M), mm) then
    HMFTracePrecomputation(M,[mm]);
    vprintf HilbertModularForms, 1 :
      "running precomputation for ideal %o. \n", IdealOneLine(mm);
  end if;
  Indexforsum := TracePrecomputation(M)[mm][aa];
  HandW := ClassNumbersPrecomputation(M);

  // Summation
  Sumterm := 0;
  for StoredData in Indexforsum do

    /*
    // Preliminaries
    b := StoredData[1];
    a := StoredData[2];
    D := b^2 - 4*a;

    // Classgroup values
    hkey := StoredData[3];
    Values := HandW[hkey];
    h := Values[1]; // Class number of quadratic extension K/F
    w := Values[2]; // Unit index of quadratic extension K/F
    ZK := Values[3]; // Used for Artin Symbol
    DD := Values[4]; // Discriminant
    ff := Sqrt((D*ZF)/DD); // Conductor
    */

    // Preliminaries
    b := StoredData[1];
    a := StoredData[2]; // x^2 + bx + a
    ZK := StoredData[5]; // Used for Artin Symbol
    ff := StoredData[6]; // Conductor
    h := StoredData[7]; // Class number of quadratic extension K/F
    w := StoredData[8]; // Unit index of quadratic extension K/F

    ///////////////////  Helper Functions //////////////////////

    // Weightfactor
    Weightfactor := function(b,a,l)
      _<x> := PowerSeriesRing( RealField(k[1] + 20), k[1] + 20); // extend with weight
      P := 1/(1 + b*x + a*x^2);
      return Coefficient(P,l);
    end function;

    // Artin Symbol
    function ArtinSymbol(pp)
      if IsSplit(pp,ZK) then return 1;
      elif IsRamified(pp,ZK) then return 0;
      else return -1; end if;
    end function;

    // Constant — FIXME: Remove Round?
    C := (h/w) * Round( &*[ Weightfactor( Evaluate(b,places[i]), Evaluate(a,places[i]), k[i]-2 ) : i in [1..n]] );

    // Factor of 2 since computation is the same for x^2 +/- bx + a.
    if b ne 0 then
      C *:= 2;
    end if;

    // Conductor Sum
    conductorsum := 0;
    for bb in Divisors( ideal< ZF | ff * aa^(-1) > ) do
      // Term from class number of order -> class number of maximal order
      term := Norm(bb) * (&*([1] cat [1 - ArtinSymbol(pp[1]) * Norm(pp[1])^(-1) : pp in Factorization(bb)]));
      // Embedding numbers
      for pair in NNfact do
        pp := pair[1];
        e := pair[2];
        f := Valuation(bb,pp); // Conductor
        g := Valuation(Discriminant(ZK),pp); // Valuation of discriminant // Change to DD eventually
        term *:= OptimalEmbeddings(e, 2*f, g, pp, ZK);
      end for;
      conductorsum +:= term;
    end for;

    // Add to Sumterm
    Sumterm +:= C * conductorsum;
  end for;

  // Trace is Constant term + Sum term
  tr := ConstantTerm(Mk,mmaa) + Sumterm;
  return tr;
end intrinsic;


///////////////////////////////////////////////////
//                                               //
//       Subroutines for the Trace Formula       //
//                                               //
///////////////////////////////////////////////////

/*

Helper functions

  * ConstantTerm (TraceProduct and PrecompTraceProduct)
    - Computes a constant term for Tr T(mm) where mm is a square.

  * CorrectionFactor (TraceProduct and PrecompTraceProduct)
    - **** Not Implemented yet  *****
    - Correction factor for spaces with k = (2,..,2) and chi = 1. I think the formula computes the trace on M_k(NN) as opposed to S_k(NN) - Talks to JV about Eisenstein series.


Index of Summation

  * IndexOfSummation (TraceProduct)
    - Computes all extensions of the forms x^2 (+/-) bx + a where (a) = mm * aa^2, b in aa, and the conductor ff is divisible by aa where aa is a representative from the class group.

  * IndexOfSummation (PrecompTraceProduct)
    - Computes all extensions of the forms x^2 + bx + a where (a) = mm * aa^2, b in aa where aa is a representative from the class group.
    - Subroutine: IdealCMExtension
      - Computes x^2 + bx + a where b in aa


Embedding Numbers

  * EmbeddingNumbers (TraceProduct)
    - Computes embedding number for an order x^2 + bx + a.

  * PolynomialMaximalOrder (TraceProduct)
    - Computes a polynomial for the local max order of in the extension (ZK)_pp / ZF_pp above a prime pp

  * OptimalEmbeddingNumbers (PrecompTraceProduct)
    - Computes embedding number for an order x^2 + bx + a using a formula.
    - Subroutine: OptimalEmbeddingsOdd
    - Subroutine: OptimalEmbeddingsEven


Class Group and Unit Index

  * ClassNumberandUnitIndex: (PrecompTraceProduct)
    - Computes the class number and unit index for precomputations

*/


///////////////////////////////////////////////////
//                                               //
//              Helper Functions                 //
//                                               //
///////////////////////////////////////////////////

// Constant Term
intrinsic ConstantTerm(Mk::ModFrmHilD, mm::RngOrdIdl) -> Any
  {Constant term for Summation}

  // check mm = aa^2 where aa is principal
  boo, aa := IsSquare(mm);
  if boo then
    boo := IsPrincipal(aa);
  end if;
  // If checks fail - return 0
  if not boo then
    return 0;
  end if;

  // Preliminaries
  M := Parent(Mk);
  NN := Level(Mk);
  k := Weight(Mk);
  F := BaseField(Mk);
  ZF := Integers(Mk);
  n := Degree(F);
  Disc := Discriminant(ZF);
  h := ClassNumber(F); // This needs to be stored

  // Constant term
  C0 := h * Norm(NN) * Abs(DedekindZetaExact(F,-1)) / 2^(n-1); // Thanks for Zeta(F,-1)!
  C0 *:= &*[ i-1 : i in k ];
  C0 *:= &*( [1] cat [1 + Norm(p[1])^(-1) : p in Factorization(NN)] );
  C0 *:= Norm(mm) ^ ( k[1] div 2 - 1 ); // Normalization factor

  return C0;
end intrinsic;


/*
intrinsic CorrectionFactor(Mk::ModFrmHilD, mm::RngOrdIdl) -> Any
  {Correction factor for parallel weight 2 and chi = 1}
  // Preliminaries
  k := Weight(Mk);
  F := BaseField(Mk);
  n := Degree(F);
  // If all ki = 2 then correction factor appears (see Arenas)
  if Set(k) eq {2} then
    return (-1)^(n+1)*&+([ Norm(dd) : dd in Divisors(mm)]);
  else
    return 0;
  end if;
end intrinsic;
*/


//////////////////////////////////////////////////////////
//                                                      //
//      Index of Summation for Trace Formulas           //
//                                                      //
//////////////////////////////////////////////////////////

// Index of Summation for Product
/* Returns representatives for all of the CM-extensions of the form x^2 +/- tx + nu where n
is totally positive generator for the fractional ideal representing the Hecke operator and
u comes form a set of representative for the totally positive units modulo squares. */

//FIXME: Refactor IndexOfSummation and PrecompIndexOfSummation so that they have a common core
intrinsic IndexOfSummation(M::ModFrmHilDGRng, mm::RngOrdIdl, aa::RngOrdIdl) -> SeqEnum
  {Computes all a,b for which x^2 + bx + a is used in the summation for T(mm) and P(aa)}
  // Preliminaries
  F := BaseField(M);
  ZF := Integers(M);
  _<x> := PolynomialRing(ZF);
  U, mU := UnitGroup(ZF);
  Ugens := [mU(u) : u in Generators(U)];

  // Totally positive units mod squares
  TotallyPositiveUnits := [];
  for v in CartesianPower([0,1],#Ugens) do
    unitelt := &*[Ugens[i]^v[i] : i in [1..#Ugens]];
    if IsTotallyPositive(unitelt) then
      Append(~TotallyPositiveUnits,unitelt);
    end if;
  end for;

  // Finding a totally positive generator for mm
  bool, a := IsNarrowlyPrincipal(mm*aa^2);
  require bool : Sprintf("Ideal %o is not narrowly principal", IdealOneLine(mm));
  a := ReduceShintaniMinimizeTrace(a)[1];

  // Looping over all totally positive generators of the form au for u a totally positive unit mod squares
  Indexforsum := [ [b,a*u] : b in IdealCMExtensions(M, a*u, 1*ZF), u in TotallyPositiveUnits];
  Indexforsum cat:= [ [-i[1], i[2]] : i in Indexforsum  | i[1] ne 0 ];  // Add x^2 +/- bx + au

  // Remove all orders x^2 + bx + a where 1) aa does not divide conductor ff or 2) b is not aa
  L := [];
  for pair in Indexforsum do
    b := pair[1];
    a := pair[2];
    D := b^2-4*a;
    K := ext<F | x^2 - D >;
    ZK := Integers(K);
    DD := Discriminant(ZK);
    ff := Sqrt((D*ZF)/DD); // Conductor
    if IsIntegral( ff * aa^(-1) ) and b in aa then
      L cat:= [pair];
    end if;
  end for;
  return L;
end intrinsic;



intrinsic PrecompIndexOfSummation(M::ModFrmHilDGRng, mm::RngOrdIdl, aa::RngOrdIdl) -> SeqEnum
  {Computes the a,b for which x^2 + bx + a is used in the summation}

  // Preliminaries
  F := BaseField(M);
  ZF := Integers(M);
  U,mU := UnitGroup(ZF);
  Ugens := [mU(u) : u in Generators(U)];

  // Totally positive units mod squares
  TotallyPositiveUnits := [];
  for v in CartesianPower([0,1],#Ugens) do
    unitelt := &*[Ugens[i]^v[i] : i in [1..#Ugens]];
    if IsTotallyPositive(unitelt) then
      Append(~TotallyPositiveUnits,unitelt);
    end if;
  end for;

  // Totally positive generator for mm * aa ^ 2
  bool, a := IsNarrowlyPrincipal( mm * aa^2 );
  require bool : Sprintf("Ideal %o is not narrowly principal", IdealOneLine(mm));
  a := ReduceShintaniMinimizeTrace(a)[1];

  // Index for summation
  return [[b,a*u] : b in IdealCMExtensions(M,a*u,aa), u in TotallyPositiveUnits];
end intrinsic;



intrinsic IdealCMExtensions(M::ModFrmHilDGRng, a::RngElt, aa::RngOrdIdl) -> SeqEnum
  {Computes all elements b satifying b^2 << 4a, but only yields one of +/-b}
  F := BaseField(M);
  ZF := Integers(M);
  places := Places(M);
  // half of square with sides 2sqrt(a).
  XLB := -2*Sqrt(Evaluate(a,places[1]));
  YLB := 0;
  XUB := 2*Sqrt(Evaluate(a,places[1]));
  YUB := 2*Sqrt(Evaluate(a,places[2]));
  T := ElementsInABox(M, aa, XLB, YLB, XUB, YUB);
  T := [ i : i in T | i^2-4*a ne 0]; // Zero is "technically" not totally positive for this computation
  return T;
end intrinsic;




///////////////////////////////////////////////////
//                                               //
//             Embedding Numbers                 //
//                                               //
///////////////////////////////////////////////////

/////////////////////////////////// Embedding Numbers //////////////////////////////////////////////

intrinsic EmbeddingNumbers(n::RngOrdElt, m::RngOrdElt, pp::RngOrdIdl, e::RngIntElt) -> Any
  {Returns the optimal embeddings of x^2+nx+m into an order of level pp^e}
  // FIXME: Clean up code
  // requirements
  require IsPrime(pp): "Not prime";
  // Preliminaries
  ZF := Ring(Parent(pp));
  D := n^2-4*m;
  Q,mQ := quo< ZF | pp^e >;
  Q1,mQ1 := quo< ZF | pp^(e+1) >;
  // roots of x^2+nx+m mod pp^e
  L := [ t@@mQ : t in Q | (t^2 + mQ(n)*t + mQ(m)) eq mQ(0) ];
  // If d is a unit then LQ — else LQ + image of elements in LQ1 which restrict down.
  if Valuation(D,pp) eq 0 then
    return #L;
  else
    L1 := [ t@@mQ1 : t in Q1 | (t^2 + mQ1(n)*t + mQ1(m)) eq mQ1(0) ];
    L1res := { mQ(i) : i in L1};
    return #L + #L1res;
  end if;
end intrinsic;



intrinsic PolynomialMaximalOrder(n::RngOrdElt, m::RngOrdElt, ZF::RngOrd, pp::RngOrdIdl) -> Any
  {Given a order ZK = x^2 + nx + m over ZF, computes a polynomial x^2 + n0x + m0 for the maximal order in the completion ZK_pp over ZF_pp}
  // Preliminaries
  D := n^2 - 4 * m;
  F := FieldOfFractions(ZF);
  _<x> := PolynomialRing(ZF);
  K := ext< F | x^2 - D >;
  ZK := Integers(K);
  qq := Factorization(pp * ( 1 * ZK ))[1][1]; // qq is the prime above pp
  /* Check if Split
    Yes: return x^2 - 1 if pp odd
         return seperate algorithm if pp even
    No -> Check if x^2 - D is ramified.
      Yes: return unformizer. // Ramified
      No: return generator for ZF / pi. // Inert */
  if IsSplit(qq) then
    // qq is even
    if Norm(pp) mod 2 eq 0 then
      // Case 1: Local algebra F_2 is split. Return x^2 - x - 4
      if IsSplit(pp) then
        n0 := ZF ! -1;
        m0 := ZF ! -4;
      // Case 2: Local algebra F_2 is inert. Return x^2 + x - 1
      elif IsInert(pp) then
        n0 := ZF ! 1;
        m0 := ZF ! -1;
      /* Case 3: Local algebra F_2 is ramified. Find an equivalent quadratic extension of Q2.
      Construct biquadratic field and use minimal polynomial for ring of integers of the 3rd quadratic field. */
      else
        for d in { 1, 2, 5, 6, 10, 14 } do
          L := ext< F | x^2 + d >;
          ZL := Integers(L);
          ppl := pp * ( 1 * ZL );
          if #Factorization(ppl) eq 2 then
            Q := QuadraticField( -Discriminant(F) * d );
            poly := MinimalPolynomial(Integers(Q).2);
            coef := Coefficients(poly);
            n0 := ZF ! coef[2];
            m0 := ZF ! coef[1];
            break;
          end if;
        end for;
      end if;
    // qq is odd
    else
      n0 := ZF ! 0;
      m0 := ZF ! -1;
    end if;
  elif IsRamified(qq) then
    pi := UniformizingElement(qq);
    minpoly := MinimalPolynomial(pi);
    coef := Coefficients(minpoly);
    n0 := coef[2];
    m0 := coef[1];
  else
    Fq, mFq := ResidueClassField(qq);
    G := Generator(Fq);
    minpoly := MinimalPolynomial(G@@mFq);
    coef := Coefficients(minpoly);
    n0 := coef[2];
    m0 := coef[1];
  end if;
  return n0,m0;
end intrinsic;



///////////////////////////////////// Optimal Embeddings ///////////////////////////////////////////////

intrinsic OptimalEmbeddings(e::RngIntElt, f::RngIntElt, g::RngIntElt, pp::RngOrdIdl, ZK::RngOrd) -> RngIntElt
  {Computes embedding numbers for x^2 - d * pi^(f) mod pp^e where: e is positive integers, f is positive even integer, pp is a prime ideal, and d = disc(ZK) has valuation(d,pp) = g where ZK is the ring of integers of the extension x^2 - d.}

  // Preliminaries
  q := Norm(pp); // Size of residue field
  Z := Integers(); // Integers (for conversion)

  // Case 1 : p is odd
  if IsOdd(q) then
    if f eq 0 then
      return OptimalEmbeddingsOdd(e,f,g,pp,ZK);
    else
      return OptimalEmbeddingsOdd(e,f,g,pp,ZK) + Z!OptimalEmbeddingsOdd(e+1,f,g,pp,ZK)/q;
    end if;
  // Case 2 : p is even
  else
    if f + g eq 0 then
      return OptimalEmbeddingsEven(e,f,g,pp,ZK);
    else
      return OptimalEmbeddingsEven(e,f,g,pp,ZK) + Z!OptimalEmbeddingsEven(e+1,f,g,pp,ZK)/q;
    end if;
  end if;
end intrinsic;



intrinsic OptimalEmbeddingsOdd(e::RngIntElt, f::RngIntElt, g::RngIntElt, pp::RngOrdIdl, ZK::RngOrd) -> RngIntElt
  {Returns all solutions to x^2 - D mod pp^e where D = d*pi^f}

  // Size of residue field
  q := Norm(pp);

  // Artin Symbol
  function ArtinSymbol(pp)
    if IsSplit(pp,ZK) then return 1; // Split: Return 1
    elif IsRamified(pp,ZK) then return 0; // Ramified: Return 0
    else return -1; end if; // Inert: Return -1
  end function;

  // Embedding Numbers
  if f + g ge e then // Case 1 : f >= e
    N := q^(Floor(e/2));
  else // Case 2 : f < e
    N := q^( ExactQuotient(f,2) ) * ArtinSymbol(pp) * (1 + ArtinSymbol(pp));
  end if;
  return N;
end intrinsic;



intrinsic OptimalEmbeddingsEven(e::RngIntElt, f::RngIntElt, g::RngIntElt, pp::RngOrdIdl, ZK::RngOrd) -> RngIntElt
  {Returns all solutions to x^2 - D mod pp^e where D = d*pi^(g+f)}

  // Preliminaries
  q := Norm(pp); // Size of residue field
  ZF := Order(pp);
  v := Valuation(2*ZF,pp); // Valuation of 2*ZF

  // Artin Symbol
  function ArtinSymbol(pp)
    if IsSplit(pp,ZK) then return 1; // Split: Return 1
    elif IsRamified(pp,ZK) then return 0; // Ramified: Return 0
    else return -1; end if; // Inert: Return -1
  end function;

  // Embedding Numbers
  if g + f ge (e + 2*v) then // Case 1 : g + 2f >= e + 2v
    N := q^(Floor(e/2));
  else // Case 2 : g + 2f < e + 2v
    if IsOdd(g) then // Subcase 2.1 : g is odd
      N := 0;
    else // Subcase 2.2 : g is even
      if e le (f + 1 - ArtinSymbol(pp)^2) then // Subsubcase 2.2.1 e <= f when pp is split or inert and e <= 2f+1 when pp is ramified
        N := q^(Floor(e/2));
      else // Subsubcase 2.2.2 e > 2f when pp is split or inert and e > f+1 when pp is ramified
        N := q^( ExactQuotient(f,2) ) * ArtinSymbol(pp) * (1 + ArtinSymbol(pp) );
      end if;
    end if;
  end if;
  return N;
end intrinsic;




///////////////////////////////////////////////////
//                                               //
//         Class Number and Unit Index            //
//                                               //
///////////////////////////////////////////////////

intrinsic ClassNumberandUnitIndex(M::ModFrmHilDGRng, K::FldNum, D::RngQuadElt, ZF::RngQuad, hplus::RngIntElt) -> Any
  {Returns the class number and the unit index 2[Z_K^* : Z_F^*] = #mu_K [Z_K^* : mu_K Z_F^*]}
  /* This takes as input
        - K/F = a number field defined as a degree 2 extension of a totally real field F
        - D = discriminant of a defining polynomial f(x) for K
        - ZF = ring of integers of F
        - hplus = the narrow class number of F ** Note : that this is not critical for this function, can removed or or set to optional parameter **
  */

  // Preliminaries //
  // Magma requires absolute extensions for class number and units
  Kabs := AbsoluteField(K);
  _, mKabs := IsIsomorphic(Kabs,K);

  // Class group
  h := ClassNumber(Kabs);

  // Roots of unity
  mu_K, mapmu_K := TorsionUnitGroup(Kabs); // roots of unity
  w := #mu_K; // size of the unity group

  // The unit index is either w or 2*w.
  unitindex := w;

  // The lines with ////////// can be removed
  /* These lines with are skipping this computation when the narrow class
  number hplus is odd — since we already have the narrow class number stored */
  if hplus mod 2 eq 0 then  //////////

    // Now we set the element B
    twopower := 2^Valuation(w,2);
    if twopower eq 2 then
      B := D;
    else
      // We now create a generator for mu_K(2) the 2-power roots of unity
      g := mu_K.1;
      // oddpartw := [p[1]^p[2] : p in Factorization(w) | p[1] ne 2];
      oddpart := Integers()!(w/twopower);
      zeta_2 := mKabs(mapmu_K(oddpart*g)); // zeta_2 is now an element of a CM-extension K/F
      B := Norm(1 + zeta_2);
      // B := 2 + zeta_2 + zeta_2^(-1); // this is the norm from K to F — should be equivalent to 1 + zeta_2 + 1/zeta_2
    end if;

    // the factor 2 comes into play only when B*ZF = aa^2 and aa is principal
    issquare, aa := IsSquare(B*ZF);
    if issquare eq true then
      if IsPrincipal(aa) then // Edgar: Narrowly?
        unitindex *:= 2;
      end if;
    end if;
  end if; //////////

  // return
  return h, unitindex;
end intrinsic;



///////////////////////////////////////////////////
//                                               //
//               Extra Trace code                //
//                                               //
///////////////////////////////////////////////////


/*
intrinsic TraceChecker(Mk::ModFrmHilD, mm::RngOrdIdl) -> Any
  {Produces the trace of mm on the space Mk}

  // Initialize
  k := Weight(Mk);
  NN := Level(Mk);
  chi := Character(Mk)^(-1); // CHECKME: I think we want inverse here
  OK := Parent(chi)`TargetRing; // CHECKME: This is weird, but should produce coefficient ring for Hecke Character
  F := BaseField(Mk);
  ZF := Integers(F);
  C,mC := ClassGroup(F); // class group
  reps := [ mC(i) : i in C ]; // class group representatives
  MJV := HilbertCuspForms(F, NN, k);
  Tmm := HeckeOp(Mk,mm);

  // loop over class group reps and take Trace[ T(mm) * P(aa) ] where T(mm) is the mth hecke operator and P(aa) is the diamond operator
  if mm eq 1*ZF then
    tr := (1/#C) * &+[ chi(aa) * (OK ! Trace(DiamondOperator(MJV,aa))) : aa in reps ];
  else
    tr := (1/#C) * &+[ chi(aa) * (OK ! Trace(Tmm * DiamondOperator(MJV,aa))) : aa in reps ];
  end if;

  return tr;

end intrinsic;
*/


// trace recursion function
// ****** Needs Testing ***********
intrinsic TraceRecurse(Mk::ModFrmHilD, mm::RngOrdIdl, nn::RngOrdIdl) -> Any
  {Computes the trace of T(pp)^r * T(pp)^s on the space Mk}

  // mm = 0 or nn = 0 return 0
  if IsZero(mm) or IsZero(nn) then
    return 0;
  end if;

  // initialize
  k := Weight(Mk);
  NN := Level(Mk);
  F := BaseField(Mk);
  ZF := Integers(F);
  C,mC := ClassGroup(F); // class group
  Creps := [ mC(i) : i in C ]; // class group representatives
  chi := Character(Mk)^(-1);
  ZK := Parent(chi)`TargetRing; // Coefficient ring for the range of the Hecke Character

  // requirements
  require #Set(k) eq 1: "Not implemented for nonparallel weights";

  // convert pp to class group rep
  function Classrep(aa)
    return [ bb : bb in Creps | IsPrincipal(bb*aa^(-1)) ][1];
  end function;

  // Greedy Algorithm - Store factorizations
  cc := GCD(mm,nn);
  mmp := &*([1*ZF] cat [ p[1]^p[2] : p in Factorization(mm) | not cc subset p[1]] ) ; // coprime to nn part
  nnp := &*([1*ZF] cat [ p[1]^p[2] : p in Factorization(nn) | not cc subset p[1]] ) ; // coprime to mm part
  ccstar := mmp * nnp;
  tuples := [ [* 1, ccstar, 1*ZF *] ];
  for pps in Factorization(cc) do
    // prime
    pp := pps[1];
    require not NN subset pp: "prime is a subset of the level";
    r := Valuation(nn,pp);
    s := Valuation(mm,pp);
    // Loop
    newtuples := [];
    for i in [0..Min(r,s)] do
      for tuple in tuples do
        a := tuple[1];
        b := tuple[2];
        c := tuple[3];
        newtuples cat:= [ [*  a * Norm(pp)^(i * (k[1] - 1)), b * pp^(r + s - 2*i), c * pp^i  *] ];
      end for;
    end for;
    tuples := newtuples;
  end for;

  // take product
  ans := 0;
  for aa in Creps do
    for t in tuples do
      qq := Classrep(t[3] * aa);
      ans +:= (1 / Norm(qq)) ^ (k[1]-2) * chi(aa) * t[1] * PrecompTraceProduct(Mk, t[2], qq);
    end for;
  end for;
  ans *:= (1/#C);

  return ans;

end intrinsic;





intrinsic HeckeOp(Mk::ModFrmHilD, mm::RngOrdIdl) -> Any
  {Produces the Hecke operator mm on the space Mk}

  // initialize
  k := Weight(Mk);
  NN := Level(Mk);
  F := BaseField(Mk);
  ZF := Integers(F);
  Factmm := Factorization(mm);
  MJV := HilbertCuspForms(F, NN, k);

  // corner case
  if mm eq 1*ZF then
    return DiamondOperator(MJV,1*ZF);
  end if;

  // loop
  L := [];
  for pair in Factmm do

    // initialize
    pp := pair[1];
    e := pair[2];

    // first hecke matrix
    T1 := HeckeOperator(MJV, pp);
    if e eq 1 then
      L cat:= [T1];
      continue;
    elif NN subset pp then
      L cat:= [T1^e];
      continue;
    end if;

    // recurse
    D := DiamondOperator(MJV,pp);
    T2 := T1 * T1 - Norm(pp)^(k[1] - 1) * D;

    // loop
    t := 2;
    Tprev := T2;
    Tprev2 := T1;
    while t lt e do
      Tfut := Tprev * T1 - Norm(pp)^(k[1] - 1) * D * Tprev2;
      // update
      Tprev2 := Tprev;
      Tprev := Tfut;
      t +:= 1;
    end while;
    L cat:= [ Tprev ];
  end for;
  ans := &*L;
  return ans;
end intrinsic;


/*
///// Trace Forms ////////////


intrinsic HeckeTraceForm(Mk::ModFrmHilD) -> ModFrmHilDElt
  {Creates the trace form in the space Mk}
  M := Parent(Mk);
  ZF := Integers(M);
  Q := Rationals();
  coeffs := AssociativeArray();
  // run trace precomputation
  PrecomputeTraceForm(M);
  for bb in NarrowClassGroupReps(M) do
    coeffs[bb] := AssociativeArray();
    for nu->nn in ShintaniRepsIdeal(M)[bb] do
      if not IsZero(nn) then
        print Norm(nn), Trace( HeckeOp(Mk,nn) );
        coeffs[bb][nu] := Q ! Trace( HeckeOp(Mk,nn) );
      else
        coeffs[bb][nu] := 0;
      end if;
    end for;
  end for;
  return HMF(Mk, coeffs);
end intrinsic;


intrinsic BadPrecompTraceProduct(Mk::ModFrmHilD, mm::RngOrdIdl, aa::RngOrdIdl) -> Any
  {Computes trace of T(mm) * P(aa) for Hecke operator T(mm) and Diamond operator P(aa) using precomputations.}

  // If mm * aa^2 = 0 or is not narrowly principal then return 0
  mmaa := mm * aa^2;
  if IsZero(mmaa) or not IsNarrowlyPrincipal(mmaa) then
    return 0;
  end if;

  // Space Preliminaries
  M := Parent(Mk);
  NN := Level(Mk);
  NNfact := Factorization(NN);
  k := Weight(Mk);
  F := BaseField(Mk);
  ZF := Integers(Mk);
  n := Degree(F);
  places := Places(M);
  _<x> := PolynomialRing(ZF);

  // Check precomputations
  if not IsDefined( TracePrecomputation(M), mm) then
    print "running precomputation for ideal     ", mm;
    HMFTracePrecomputation(M,[mm]);
  end if;
  Indexforsum := TracePrecomputation(M)[mm][aa];

  // Summation
  Sumterm := 0;
  for StoredData in Indexforsum do

    // Preliminaries
    b := StoredData[1];
    a := StoredData[2]; // x^2 + bx + a
    ZK := StoredData[5]; // Used for Artin Symbol
    ff := StoredData[6]; // Conductor
    h := StoredData[7]; // Class number of quadratic extension K/F
    w := StoredData[8]; // Unit index of quadratic extension K/F

    ///////////////////  Helper Functions //////////////////////

    // Weightfactor
    Weightfactor := function(b,a,l)
      _<x> := PowerSeriesRing(RealField(k[1]+20),k[1]+20); // extend with weight
      P := 1/(1 + b*x + a*x^2);
      return Coefficient(P,l);
    end function;

    // Artin Symbol
    function ArtinSymbol(pp)
      if IsSplit(pp,ZK) then return 1;
      elif IsRamified(pp,ZK) then return 0;
      else return -1; end if;
    end function;

    // Constant
    C := (h/w) * (&*[ Weightfactor( Evaluate(b,places[i]), Evaluate(a,places[i]), k[i]-2 ) : i in [1..n]]);
    // We do one computation for x^2 - bx + a and x^2 + bx + a since the embedding numbers are the same
    if b ne 0 then C *:= 2; end if;

    // Conductor Sum
    conductorsum := 0;
    for bb in Divisors( ideal< ZF | ff * aa^(-1) > ) do
      // Term from class number of order -> class number of maximal order
      term := 1;
      term *:= Norm(bb) * (&*([1] cat [1 - ArtinSymbol(pp[1]) * Norm(pp[1])^(-1) : pp in Factorization(bb)]));
      // Embedding numbers
      for pair in NNfact do
        pp := pair[1];
        e := pair[2];
        f := Valuation(bb,pp); // Conductor
        g := Valuation(Discriminant(ZK),pp); // Valuation of discriminant
        term *:= OptimalEmbeddings(e, 2*f, g, pp, ZK);
      end for;
      conductorsum +:= term;
    end for;

    // Add to Sumterm
    Sumterm +:= C * conductorsum;
  end for;

  // Trace is Constant term + Sum term
  tr := Round( ConstantTerm(Mk,mmaa) + Sumterm );

  // adjust for bad primes ( This can be toggled on / off still produces a trace )
  cc := GCD(NN,mm);
  if cc ne 1*ZF then
    Badness := [ dd : dd in Divisors(ideal< ZF | NN * cc^(-1) >) | dd ne NN ];
    for dd in Badness do
        // including space
        Mdd := HMFSpace(M,dd,k);
        // "index" of Mk(dd) in Mk(NN)
        ii := ideal< ZF | NN * dd^(-1) >;
        // include new traceform at level dd into level NN
        L := [];
        for ee in Divisors(GCD(mm,ii)) do
          if ee ne 1*ZF then
            mee := ideal< ZF | mm * ee^(-1) >;
            print Norm(dd), Norm(ii), Norm(ee), Norm(mee), TraceRecurse(Mdd,ee,mee), #Divisors(ideal< ZF | ii * ee^(-1) >);
            tr -:= TraceRecurse(Mdd,ee,mee) * #Divisors(ideal< ZF | ii * ee^(-1) >);
          end if;
        end for;
    end for;
  end if;

  // return
  return tr;
end intrinsic;




intrinsic PrecompTraceProductNew(Mk::ModFrmHilD, mm::RngOrdIdl, aa::RngOrdIdl) -> Any
  {Computes trace of T(mm) * P(aa) for Hecke operator T(mm) and Diamond operator P(aa) using precomputations.}

  // If mm * aa^2 = 0 or is not narrowly principal then return 0
  mmaa := mm * aa^2;
  if IsZero(mmaa) or not IsNarrowlyPrincipal(mmaa) then
    return 0;
  end if;

  // Space Preliminaries
  M := Parent(Mk);
  NN := Level(Mk);
  k := Weight(Mk);
  F := BaseField(Mk);
  ZF := Integers(Mk);

  ///////////////////  Helper Functions //////////////////////

  // sign of (p1^e1) * (p2^e2) * ... * (pn^en) = (-1) ^ (e1 + e2 + ... + en)
  sgn := function(aa)
    if aa eq 1*ZF then
      return 1;
    else
      return (-1) ^ &+[i[2] : i in Factorization(aa)];
    end if;
  end function;

  ans := 0;
  for dd in Divisors(NN) do
      Mdd := HMFSpace(M,dd,k);
      ii := ideal< ZF | NN * dd^(-1) >;  // index of dd in NN
      ans +:= sgn(dd) * Trace( Mdd, mm : precomp := true) * #Divisors(ii);
  end for;

  return ans;
end intrinsic;


*/

//////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////
//                                               //
//                    Extras                     //
//                                               //
///////////////////////////////////////////////////

/*
intrinsic NewTraceForm(Mk::ModFrmHilD) -> ModFrmHilDElt
  {Creates the trace form in the space Mk}
  M := Parent(Mk);
  ZF := Integers(M);
  Q := Rationals();
  coeffs := AssociativeArray();
  for bb in NarrowClassGroupReps(M) do
    coeffs[bb] := AssociativeArray();
    for nu->nn in ShintaniRepsIdeal(M)[bb] do
      coeffs[bb][nu] := PrecompTraceProductNew(Mk, nn, 1*ZF);
    end for;
  end for;
  return HMF(Mk, coeffs);
end intrinsic;



intrinsic NewformTrace(f::ModFrmHilDElt) -> ModFrmHilDElt
  {returns the full Galois orbit of a modular form over Q}
  fSpace := Parent(f);
  M := Parent(fSpace);
  k := Weight(fSpace);
  require Set(k) ne {2}: "Only implemented when k =/= 2";
  CF := CoefficientField(f);

  result := [];
  bbs := NarrowClassGroupReps(M);
  coeff := Coefficients(f);
  for bb in bbs do
    for nn in Keys(Coefficients(f)[bb]) do
      coeff[bb][nn] := Trace(CF!coeff[bb][nn]);
    end for;
  end for;
  return HMF(fSpace,coeff);
end intrinsic;



intrinsic ActualTraceForm(Mk::ModFrmHilD) -> ModFrmHilDElt
  {Returns that Trace form as computed by Magma}
  require Set(Weight(Mk)) ne {2}: "Not implemented when k = (2,..,2)";
  //require Norm(Level(Mk)) eq 1: "Only implemented in trivial level";
  N := NewCuspForms(Mk);
  if #N eq 0 then
    return HMFZero(Mk);
  else
    return &+[NewformTrace(i) : i in N];
  end if;
end intrinsic;


intrinsic TwoLinearDependence(List::SeqEnum[ModFrmHilDElt]) -> SeqEnum[RngIntElt]
  {finds a small non-trivial integral linear combination between components of v away from nn. If none can be found return 0.}
  M := GradedRing(List[1]);
  ZF := Integers(M);
  bbs := NarrowClassGroupReps(M);
  CoeffLists := [[] : i in [1..#List]];
  for bb in bbs do
    for nn in IdealsByNarrowClassGroup(M)[bb] do // Edgar: are you sure?
      if nn ne 0*ZF then
        for i in [1..#List] do
          Append(~CoeffLists[i], Coefficients(List[i])[bb][nn]);
        end for;
      end if;
    end for;
  end for;
  return LinearDependence(CoeffLists);
end intrinsic;

*/
