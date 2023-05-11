
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
  return (1/#C) * &+[ 1 / Norm(aa) ^ (k[1]-2) * chi(aa) * (ZK ! TraceProduct(Mk, mm, aa : precomp := precomp )) : aa in CReps ];

end intrinsic;



///////////////////////////////// ModFrmHilD: TraceProduct ////////////////////////////////////////////

intrinsic TraceProduct(Mk::ModFrmHilD, mm::RngOrdIdl, aa::RngOrdIdl : precomp := false) -> RngElt
  {Computes Trace[ T(mm) * P(aa) ] where T(mm) is the mth hecke operator and P(aa) is the diamond operator}

  // If mm * aa^2 = 0 or is not narrowly principal then return 0
  mmaa := mm * aa^2;
  if IsZero(mmaa) or not IsNarrowlyPrincipal(mmaa) then
    return 0;
  end if;

  // Preliminaries
  M := Parent(Mk);
  NN := Level(Mk);
  NNfact := Factorization(NN);
  k := Weight(Mk);

  // Index for summation
  Indexforsum := precomp select TracePrecomputationByIdeal(M,mm)[aa] else IndexOfSummation(M, mm, aa);

  Sumterm := 0;
  for data in Indexforsum do
    t, n := Explode(data);
    wk := Coefficient(WeightFactor(n,t,k[1]+2),k[1]); // Weight Factor
    // Embedding numbers
    if precomp then
      emb := PrecompEmbeddingNumberOverUnitIndex(M, data, NNfact, aa);
      emb := t eq 0 select emb else 2*emb; // Factor of 2 accounts for x^2 +/- bx + a.
    else
      emb := EmbeddingNumberOverUnitIndex(M, data, NNfact, aa);
    end if;
    Sumterm +:= wk * emb;
  end for;

  // Trace is Constant term + Sum term
  tr := ConstantTerm(Mk,mmaa) + Sumterm;
  return tr;
end intrinsic;


/////////////////////////////// ModFrmHilD: HilberSeriesCusp /////////////////////////////////////////

intrinsic HilbertSeriesCusp(M::ModFrmHilDGRng, NN::RngOrdIdl : prec:=false) -> RngSerPowElt
  { returns the hilbert series for the dimension of the space of cusp forms of level NN }

  R<T> := PowerSeriesRing(Rationals());
  F := BaseField(M);
  ZF := Integers(M);
  n := Degree(F);
  Disc := Discriminant(ZF);
  h := ClassNumber(F);

  // for consistency with the rest of the code for trace formulas
  mm := 1*ZF; // hecke operator
  aa := 1*ZF; // diamond operator

  // list of pairs (u,t) that we will sum over
  // FIXME maybe do (u,t) and (u,-t) in one go
  vprintf HMFTrace : "Computing index of summation...";
  vtime HMFTrace:
  pairs := IndexOfSummation(M, mm, aa);

  // degree(1/T^2) + degree(\sum_{k \in 2Z_>0} (k-1)^n T^k) + #pairs*degree(sum D_k)
  // the denominator of sum D_k has degree 2n and numerator at most 2n-1
  degree := 2 + (4*(n + 1)) + 2*2^n*#pairs;
  if prec cmpeq false then
    prec := 2*degree + 1 + 20; // for sanity check later on
    reconstruct := true;
  else
    reconstruct := false;
  end if;

  // Correction term for weight 2
  res := (-1)^(n+1) * NarrowClassNumber(M)*T^2;

  // Constant term
  B := h * Norm(NN) * Abs(DedekindZetaExact(F,-1)) / 2^(n-1);
  B *:= &*( [1] cat [1 + Norm(p[1])^(-1) : p in Factorization(NN)] );

  res +:= B*R!([(k mod 2 eq 0 and k gt 0) select (k-1)^(n) else 0 : k in [0..prec]]);
  res +:= O(T^(prec + 1));


  done := Set([]);
  for pair in pairs do
  //for pair in IndexOfSummation(M, mm, aa) do
    t, u := Explode(pair);
    if [-t, u] in done then continue; end if;
    // account for (u, t) and (u, -t)
    Include(~done, pair);
    mult := t ne 0 select 2 else 1;
    // C(u,t)
    C := EmbeddingNumberOverUnitIndex(M, [t,u], Factorization(NN), aa);
    vprintf HMFTrace : "ConductorSum: <%o, %o> %o\n", u, t, EmbeddingNumberOverUnitIndex(M, [t,u], Factorization(NN), aa);
    vprintf HMFTrace : "WeightFactor: <%o, %o> %o\n", u, t, WeightFactor(u, t, prec);
    res +:= mult * C * WeightFactor(u, t, prec);
  end for;
  if reconstruct then
    R<X> := PolynomialRing(Rationals());
    b, num, den := RationalReconstruction(R!AbsEltseq(res), X^(prec + 1), prec div 2, prec div 2);
    assert b;
    assert Degree(num) + Degree(den) le degree;
    return num/den;
  else
    return res;
  end if;
end intrinsic;

intrinsic HilbertSeries(M::ModFrmHilDGRng, NN::RngOrdIdl : prec:=false) -> RngSerPowElt
  {Compute the Hilbert Series for the full space, Eisenstein and cuspidal}
  // Hilbert Series for Cusp Space
  ans := HilbertSeriesCusp(M, NN : prec:=false);
  R<X> := Parent(ans);
  // Compute the dimension of the Eisenstein Series
  Mk := HMFSpace(M,NN,[2,2]);
  n := NumberOfCusps(Mk);
  ans +:= n/(1-X^2);
  return ans;
end intrinsic;

///////////////////////////////////////////////////
//                                               //
//       Subroutines for the Trace Formula       //
//                                               //
///////////////////////////////////////////////////

/*

Helper functions

  * Weightfactor                                       (Computes a generating series for the weight factor used in the trace formula.)
  * ConstantTerm                                       (Computes a constant term for Tr T(mm) where mm is a square.)
  * CorrectionFactor  **** Not Implemented yet  *****  (Correction factor for spaces with k = (2,..,2) and chi = 1. I think the formula computes the trace on M_k(NN) as opposed to S_k(NN) - Talk to JV about Eisenstein series.)


Index of Summation

  * IndexOfSummation                                   (Computes all extensions of the forms x^2 + bx + a where (a) = mm * aa^2, b in aa where aa is a representative from the class group.)
    - IdealCMExtension                                 (Computes x^2 + bx + a where b in aa)


Embedding Numbers over Unit Index

  * Helper functions
    - FastArtinSymbol                                  (Fast implementation of artin symbol)
    - ClassNumberOverUnitIndex                         (Computes the class number and a unit index)

  * EmbeddingNumbersOverUnitIndex                      (Computes Embedding numbers for an order x^2 + bx + a over a unit index)
    - OptimalEmbeddingNumbers                          (Computes optimal embedding number for an order x^2 + bx + a using a formula.)
      * Subroutine: PolynomialforOrder                 (Computes a polynomial for the local max order of in the extension (ZK)_pp / ZF_pp above a prime pp with a conductor of bb)
      * Subroutine: PolynomialMaximalOrder             (Computes a polynomial for the local max order of in the extension (ZK)_pp / ZF_pp above a prime pp)


  * PrecompEmbeddingNumbersOverUnitIndex               (Computes Embedding numbers for an order x^2 + bx + a over a unit index)
    - OptimalEmbedding                                 (Computes optimal embedding number for an order x^2 + bx + a using a formula.)
      * Subroutine: OptimalEmbeddingsOdd
      * Subroutine: OptimalEmbeddingsEven


Class Group and Unit Index

  * ClassNumberandUnitIndex: (PrecompTraceProduct)
    - Computes the class number and unit index for precomputations

*/


///////////////////////////////////////////////////
//                                               //
//              Helper Functions                 //
//                                               //
///////////////////////////////////////////////////


// Weightfactor
intrinsic WeightFactor(u::RngElt, t::RngElt, prec::RngIntElt) -> RngElt
  { Returns a generating series for the weight factor }
  // \sum D_k T^k = 1/(1 - t*T + u*T^2)
  // returns \sum_{k <= prec} Norm(D_{k-2}) T^{k}
  res := [1, t] cat [Parent(t) | 0 : _ in [0..prec-2 + 1]];
  rm2 := res[1];
  rm1 := res[2];
  for k in [3..prec-1] do
    rm2, rm1 := Explode([rm1, t*rm1 - u*rm2]);
    res[k] := rm1;
  end for;
  R<T> := PowerSeriesRing(Rationals());
  return T^2*R![i mod 2 eq 1 select Norm(elt) else 0: i->elt in res] + O(T^(prec + 1));
end intrinsic;


// Constant Term
intrinsic ConstantTerm(Mk::ModFrmHilD, mm::RngOrdIdl) -> RngElt
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

intrinsic IndexOfSummation(M::ModFrmHilDGRng, mm::RngOrdIdl, aa::RngOrdIdl : precomp := false) -> SeqEnum
  {Computes all a,b for which x^2 + bx + a is used in the summation for T(mm) and P(aa)}
  // Preliminaries
  F := BaseField(M);
  ZF := Integers(M);
  _<x> := PolynomialRing(ZF);
  U, mU := UnitGroup(ZF);
  Ugens := [mU(u) : u in Generators(U)];

  // Totally positive units mod squares
  vprintf HMFTrace: "Computing TotallyPositiveUnits...";
  TotallyPositiveUnits := [];
  for v in CartesianPower([0,1],#Ugens) do
    unitelt := &*[Ugens[i]^v[i] : i in [1..#Ugens]];
    if IsTotallyPositive(unitelt) then
      Append(~TotallyPositiveUnits,unitelt);
    end if;
  end for;
  vprintf HMFTrace: "Done %o\n", #TotallyPositiveUnits;

  vprintf HMFTrace, 2: "Reducing shintani...";
  // Finding a totally positive generator for mm
  bool, a := IsNarrowlyPrincipal(mm*aa^2);
  require bool : Sprintf("Ideal %o is not narrowly principal", IdealOneLine(mm));
  a := ReduceShintaniMinimizeTrace(a)[1];
  vprintf HMFTrace, 2: "Done\n";

  vprintf HMFTrace, 2: "Computing Indexforsum...";
  // Looping over all totally positive generators of the form au for u a totally positive unit mod squares
  Indexforsum := [[b,a*u] : b in IdealCMExtensions(M,a*u,aa), u in TotallyPositiveUnits];
  vprintf HMFTrace, 2: "Done\n";

  // Non precomputed version - adjusted to contain both x^2 - bx + au and x^2 + bx + au.
  if not precomp then
    Indexforsum cat:= [ [-i[1], i[2]] : i in Indexforsum  | i[1] ne 0 ];
  end if;

  return Indexforsum;
end intrinsic;


intrinsic IdealCMExtensions(M::ModFrmHilDGRng, a::RngElt, aa::RngOrdIdl) -> SeqEnum
  {Computes all elements b satifying b^2 << 4a, but only yields one of +/-b}
  vprintf HMFTrace, 2: "IdealCMExtensions(M, %o, %o)\n", a, aa;
  F := BaseField(M);
  ZF := Integers(M);
  places := Places(M);
  // half of square with sides 2sqrt(a).
  XLB := -2*Sqrt(Evaluate(a,places[1]));
  YLB := 0;
  XUB := 2*Sqrt(Evaluate(a,places[1]));
  YUB := 2*Sqrt(Evaluate(a,places[2]));
  vprintf HMFTrace, 3: "computing ElementsInABox(M, aa, %o, %o, %o, %o)...", XLB, YLB, XUB, YUB;
  vtime HMFTrace, 3: T := ElementsInABox(M, aa, XLB, YLB, XUB, YUB);
  T := [ i : i in T | i^2-4*a ne 0]; // Zero is "technically" not totally positive for this computation
  vprintf HMFTrace, 2: "Done with IdealCMExtensions(M, %o, %o)\n", a, aa;
  return T;
end intrinsic;




///////////////////////////////////////////////////
//                                               //
//      Embedding Numbers over Unit Index        //
//                                               //
///////////////////////////////////////////////////

// Functions

function FastArtinSymbol(D, pp, DD)
  /* {Returns the artin symbol (K/pp) which is 0 if pp ramifies, -1, if pp splits and
  1 if pp is inert in the extension K = F(x) / (x^2 - D) where ZK has discrminant DD} */
  // D element of F for generating the field K = F(x) / (x^2 - D)
  // pp prime ideal of F
  // DD discriminant of the maximal order K
  if DD subset pp then
    return 0;
  elif IsLocalSquare(D,pp) then
    return 1;
  else
    return -1;
  end if;
end function;

function ClassNumberOverUnitIndex(M,K)
  // K CM quadratic extension of F
  // M ModFrmHilDGRng
  UF := UnitGroup(M);
  mUF := UnitGroupMap(M);
  Kabs := AbsoluteField(K);
  ZKabs := Integers(Kabs);
  UK, mUK := UnitGroup(ZKabs);
  _, mKabstoK := IsIsomorphic(Kabs,K);
  hK := ClassNumber(Kabs); // h = Class number
  // Unit index w = 2 * [ZK^* : ZF^*]
  UnitIndex := 2 * #quo< UK | [ (mKabstoK(mUF(u)))@@mUK : u in Generators(UF) ] >;
  return hK / UnitIndex;
end function;


/////////////////////////////////// Embedding Numbers over Unit index  //////////////////////////////////////////////

intrinsic EmbeddingNumberOverUnitIndex(M::ModFrmHilDGRng, data::SeqEnum, FactNN::SeqEnum, aa::RngOrdIdl) -> RngElt
  {Returns a count for the number of embeddings of the order S = ZF[x] / x^2 - tx + n into a Eichler order O(nn) of
  level NN in the definite quaternion algebra B/F with index aa up to units [O(nn)^* : ZF^*]}
  //
  // data = [t, n] coefficients for the polynomial x^2 - tx + n
  // FactNN = Factorization of the ideal NN
  // Mk HMFSpace (carries field F, ring of integers ZF, level NN, and unit group + unit group map UF, mUF)
  // aa ideal for the diamond operator
  //

  // Preliminaries
  ZF := Integers(M);
  F := BaseField(M);
  t, n := Explode(data);
  D := t^2 - 4*n;
  _<x> := PolynomialRing(ZF);
  K := ext<F | x^2 - D >;
  ZK := Integers(K);
  DD := Discriminant(ZK);
  hw := ClassNumberOverUnitIndex(M,K); // Computes h/w where h = class number of K and w = unit index of 2 * [ZK^* : ZF^*]
  ff := Sqrt((D*ZF)/DD); // Conductor

  // Sum over conductors
  conductorsum := 0;
  if ff subset aa then // check if aa divides ff
    for bb in Divisors( ideal< ZF | ff * aa^(-1) > ) do
      term := Norm(bb) * (&*([1] cat [1 - FastArtinSymbol(D,pp[1],DD) * Norm(pp[1])^(-1) : pp in Factorization(bb)]));
      // Embedding numbers
      for pair in FactNN do
        pp, e := Explode(pair); // prime and exponent
        f := Valuation(bb,pp); // Conductor
        tb, nb := PolynomialforOrder(t, n, ZF, pp, f); // Polynomial for order with conductor bb
        term *:= OptimalEmbeddingNumber(tb, nb, pp, e);
      end for;
      conductorsum +:= term;
    end for;
  end if;

  // embedding number
  embeds := hw * conductorsum;

  return embeds;
end intrinsic;


/////////////////////////////////// Embedding Numbers over Unit index (Precomputations)  //////////////////////////////////////////////

intrinsic PrecompEmbeddingNumberOverUnitIndex(M::ModFrmHilDGRng, data::SeqEnum, NNfact::SeqEnum, aa::RngOrdIdl) -> RngElt
  {Returns a count for the number of embeddings of the order S = ZF[x] / x^2 - tx + n into a Eichler order O(nn) of
  level NN in the definite quaternion algebra B/F with index aa up to units [O(nn)^* : ZF^*]}
  //
  // t, n coefficients for the polynomial x^2 - tx + n
  // NNfact = Factorization of the ideal NN for the level
  // M ModFrmHilDGRng (carries field F, ring of integers ZF, and unit group + unit group map UF, mUF)
  // aa ideal for the diamond operator
  //

  // Preliminaries
  ZF := Integers(M);
  t, n, key := Explode(data);
  h, w, DD := Explode(ClassNumbersPrecomputation(M)[key]); // h = class number of K, w = unit index of 2 * [ZK^* : ZF^*], DD = discriminant of maximal order
  D := t^2 - 4*n; // Discriminant of order
  hw := h / w; // Computes h/w where h = class number of K and w = unit index of 2 * [ZK^* : ZF^*]
  ff := Sqrt((D*ZF)/DD); // Conductor

  // Conductor Sum
  conductorsum := 0;
  for bb in Divisors( ideal< ZF | ff * aa^(-1) > ) do
    term := Norm(bb) * (&*([1] cat [1 - FastArtinSymbol(D,pp[1],DD) * Norm(pp[1])^(-1) : pp in Factorization(bb)]));
    // Embedding numbers
    for pair in NNfact do
      pp := pair[1];
      e := pair[2];
      f := Valuation(bb,pp); // Conductor
      term *:= OptimalEmbeddings(e, 2*f, DD, pp, D);
    end for;
    conductorsum +:= term;
  end for;

  // embedding number
  embeds := hw * conductorsum;

  return embeds;
end intrinsic;


/////////////////////////////////// Embedding Numbers over Unit index  //////////////////////////////////////////////

intrinsic OptimalEmbeddingNumber(n::RngOrdElt, m::RngOrdElt, pp::RngOrdIdl, e::RngIntElt) -> RngIntElt
  {Returns the optimal embeddings of x^2+nx+m into an a local order of level pp^e}
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


intrinsic PolynomialforOrder(t::RngOrdElt, n::RngOrdElt, ZF::RngOrd, pp::RngOrdIdl, f::RngIntElt) -> Any
  { Create a global polynomial x^2 + tbx + ab with local conductor f over pp }
  t0, n0 := PolynomialMaximalOrder(t, n, ZF, pp);
  pi := UniformizingElement(pp);
  t0 *:= pi^(f);
  n0 *:= pi^(2 * f);
  return t0, n0;
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

intrinsic OptimalEmbeddings(e::RngIntElt, f::RngIntElt, DD::RngOrdIdl, pp::RngOrdIdl, D::RngElt) -> RngIntElt
  {Computes embedding numbers for x^2 - d * pi^(f) mod pp^e where: e is positive integers, f is positive even integer, pp is a prime ideal, and d = disc(ZK) has valuation(d,pp) = g where ZK is the ring of integers of the extension x^2 - d.}

  // Preliminaries
  q := Norm(pp); // Size of residue field
  Z := Integers(); // Integers (for conversion)
  g := Valuation(DD,pp); // Valuation of discriminant

  // Case 1 : p is odd
  if IsOdd(q) then
    return f eq 0 select OptimalEmbeddingsOdd(e,f,g,DD,pp,D) else OptimalEmbeddingsOdd(e,f,g,DD,pp,D) + Z!OptimalEmbeddingsOdd(e+1,f,g,DD,pp,D)/q;
  // Case 2 : p is even
  else
    return f + g eq 0 select OptimalEmbeddingsEven(e,f,g,DD,pp,D) else OptimalEmbeddingsEven(e,f,g,DD,pp,D) + Z!OptimalEmbeddingsEven(e+1,f,g,DD,pp,D)/q;
  end if;
end intrinsic;



intrinsic OptimalEmbeddingsOdd(e::RngIntElt, f::RngIntElt, g::RngIntElt, DD::RngOrdIdl, pp::RngOrdIdl, D::RngElt) -> RngIntElt
  {Returns all solutions to x^2 - D mod pp^e where D = d*pi^f}

  // Size of residue field
  q := Norm(pp);

  // Embedding Numbers
  if f + g ge e then // Case 1 : f >= e
    N := q^(Floor(e/2));
  else // Case 2 : f < e
    N := q^(ExactQuotient(f,2)) * FastArtinSymbol(D, pp, DD) * (1 + FastArtinSymbol(D, pp, DD));
  end if;
  return N;
end intrinsic;



intrinsic OptimalEmbeddingsEven(e::RngIntElt, f::RngIntElt, g::RngIntElt, DD::RngOrdIdl, pp::RngOrdIdl, D::RngElt) -> RngIntElt
  {Returns all solutions to x^2 - D mod pp^e where D = d*pi^(g+f)}

  // Preliminaries
  q := Norm(pp); // Size of residue field
  ZF := Order(pp);
  v := Valuation(2*ZF,pp); // Valuation of 2*ZF

  // Embedding Numbers
  if g + f ge (e + 2*v) then // Case 1 : g + 2f >= e + 2v
    N := q^(Floor(e/2));
  else // Case 2 : g + 2f < e + 2v
    if IsOdd(g) then // Subcase 2.1 : g is odd
      N := 0;
    else // Subcase 2.2 : g is even
      if e le (f + 1 - FastArtinSymbol(D, pp, DD)^2) then // Subsubcase 2.2.1 e <= f when pp is split or inert and e <= 2f+1 when pp is ramified
        N := q^(Floor(e/2));
      else // Subsubcase 2.2.2 e > 2f when pp is split or inert and e > f+1 when pp is ramified
        N := q^( ExactQuotient(f,2) ) * FastArtinSymbol(D, pp, DD) * (1 + FastArtinSymbol(D, pp, DD));
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
      b, mKabs := IsIsomorphic(Kabs,K);
      assert b;
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
      ans +:= (1 / Norm(qq)) ^ (k[1]-2) * chi(aa) * t[1] * TraceProduct(Mk, t[2], qq : precomp := true);
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
