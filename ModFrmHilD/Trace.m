
///////////////////////////////////////////////////
//                                               //
//                 Trace Formula                 //
//                                               //
///////////////////////////////////////////////////

//////////////////// Preliminary functions /////////////////////////

// Constant Term
/* TODO
* Nonparallel weight: We have Norm(mm)^(Integers()!(k[1]/2-1)) which should be m_i^(k_i/2-1). This comes from trace on weight space
* Character: The character is on the narrow class group of modulus NN where NN is the level, but
in magma this yields 0 for ideals that are not coprime to the level and we need this to be 1. */
// Returns the constant term for the trace formula
// Notes: None
//
// TODO: Replace DedekindZetatwo call with DedekindZetaExact(K, -1);
intrinsic ConstantTerm(Mk::ModFrmHilD, mm::RngOrdIdl) -> Any
  {Constant term for Summation}
  // Preliminaries
  t := 0;
  if IsSquare(mm) then
    _,sqrtmm := IsSquare(mm);
    if IsNarrowlyPrincipal(sqrtmm) then
      t := 1;
    end if;
  end if;
  if t eq 1 then
    // More preliminaries
    M := Parent(Mk);
    NN := Level(Mk);
    k := Weight(Mk);
    F := BaseField(Mk);
    ZF := Integers(Mk);
    n := Degree(F);
    Disc := Discriminant(ZF);
    h := ClassNumber(F); // This needs to be stored

    ///////////////
    // Do something which looks like computing the exact value of Zeta(K, -1).
    
    DedekindZetatwo := DedekindZetatwo(M); // Fixed Precision (Look in DedekindZetaExact.m)
    prec := 100; // Fixed Precision — should match precision of DedekindZetatwo.
    R := RealField(prec);

    C0 := 2*DedekindZetatwo/(2*Pi(R))^(2*n); // Product is broken up into several steps
    C0 *:= h*(R!Disc)^(3/2)*Norm(NN);
    C0 := BestApproximation(C0,prec-10); // **** IMPORTANT **** Convert to rational number

    
    ///////////////
    // Conclude the computation.
    
    C0 *:= &*[i-1 : i in k];
    C0 *:= &*([1] cat [1+Norm(p[1])^(-1) : p in Factorization(NN)]);
    C0 *:= Norm(mm)^(Integers()!(k[1]/2-1));
    return C0;
  else
    return 0;
  end if;
end intrinsic;


// Correction Factor
/* For the specific case of parallel weight k = [2,2,..2] and trivial character chi = 1, then the
trace formula computes the trace on M_k(NN) as opposed to S_k(NN). This can be adjusted by using the
eisensenstein series, but I have not gotten this working correctly yet (I think it works when the narrow class group is trivial).
We don't really need this factor so I have turned this off for now.*/
// Returns a correction factor when k = [2,2,..2] and trivial character chi = 1.
// Notes: *****  Not Currently Implemented ******
intrinsic CorrectionFactor(Mk::ModFrmHilD, mm::RngOrdIdl) -> Any
  {Correction factor that appears when all ki = 2 —— taken from arenas}
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


////////////////////////////////// CM - Extensions ///////////////////////////////////////////////

// CM-Extensions

// Half of CM-Extensions
intrinsic HalfOfCMExtensions(M::ModFrmHilDGRng, a::RngElt) -> SeqEnum
  {Computes all elements b satifying b^2 << 4a, but only yields one of +/-b}
  F := BaseField(M);
  ZF := Integers(M);
  places := Places(M);
  // Every element b^2 << 4a satifies |b| < 2sqrt(a).
  // This is a square centered at the origin. We will enumerate half of it.
  XLB := -2*Sqrt(Evaluate(a,places[1])); // XLB = X lower bound
  YLB := 0;
  XUB := 2*Sqrt(Evaluate(a,places[1]));
  YUB := 2*Sqrt(Evaluate(a,places[2]));
  T := ElementsInABox(M, 1*ZF, XLB, YLB, XUB, YUB);
  T := [ i : i in T | i^2-4*a ne 0]; // Zero is "technically" not totally positive for this computation
  return T;
end intrinsic;

// Computes all CM-Quadratic fields needed for computation x^2 + tx + n with t^2 >> n
intrinsic CMExtensions(M::ModFrmHilDGRng,a::RngOrdElt) -> SeqEnum
  {Computes all elements b satifying b^2 << 4a}
  T := HalfOfCMExtensions(M, a);
  T cat:= [-i : i in T | i ne 0];
  return T;
end intrinsic;





////////////////////////////////// Index of Summation: Trace ///////////////////////////////////////////////

// Index for Trace Formula
/* Returns representatives for all of the CM-extensions of the forms x^2 + tx + nu where n
is totally positive generator for the fractional ideal representing the Hecke operator and
u comes form a set of representative for the totally positive units modulo squares. */
// Notes: This is essentially reduced by a factor of 2 in the speed trace when we indentify x^2 + tx + nu and x^2 - tx + nu
intrinsic IndexOfSummation(Mk::ModFrmHilD, mm::RngOrdIdl) -> SeqEnum
  {Computes the a,b for which x^2-bx-a is used in the summation}
  // Preliminaries
  M := Parent(Mk);
  F := BaseField(Mk);
  ZF := Integers(Mk);

  // Computing totally positive units mod squares
  U, mU := UnitGroup(ZF);
  Ugens := [mU(u) : u in Generators(U)];
  TotallyPositiveUnits := [];
  // Every totally positive unit mod squares can be written as e = u_i^a_i where a_i = 0,1 and u_i are the generators for the unit group
  // We just loop over all combinations of generators and check to see if the resulting unit is totally positive.
  for v in CartesianPower([0,1],#Ugens) do
    unitelt := &*[Ugens[i]^v[i] : i in [1..#Ugens]];
    if IsTotallyPositive(unitelt) then
      Append(~TotallyPositiveUnits, unitelt);
    end if;
  end for;

  // Finding a totally positive generator for mm
  bool, a := IsNarrowlyPrincipal(mm);
  require bool : Sprintf("Ideal %o is not narrowly principal", IdealOneLine(mm));
  a := ReduceShintaniMinimizeTrace(a)[1];

  // Looping over all totally positive generators of the form au for u a totally positive unit mod squares
  Indexforsum := &cat[[[b,a*u] : b in CMExtensions(M, a*u)] : u in TotallyPositiveUnits];

  return Indexforsum;
end intrinsic;


// Speed Index of Summation
/* Returns representatives for all of the CM-extensions of the forms x^2 +/- tx + nu where n
is totally positive generator for the fractional ideal representing the Hecke operator and
u comes form a set of representative for the totally positive units modulo squares. */
intrinsic SIndexOfSummation(M::ModFrmHilDGRng, mm::RngOrdIdl) -> SeqEnum
  {Computes the a,b for which x^2-bx-a is used in the summation}
  // Preliminaries
  F := BaseField(M);
  ZF := Integers(M);

  // Computing totally positive units mod squares
  U,mU := UnitGroup(ZF);
  Ugens := [mU(u) : u in Generators(U)];
  TotallyPositiveUnits := [];
  // Every totally positive unit mod squares can be written as e = u_i^a_i where a_i = 0,1 and u_i are the generators for the unit group
  // We just loop over all combination of generators and check to see if the resulting unit is totally positive.
  for v in CartesianPower([0,1],#Ugens) do
    unitelt := &*[Ugens[i]^v[i] : i in [1..#Ugens]];
    if IsTotallyPositive(unitelt) then
      Append(~TotallyPositiveUnits,unitelt);
    end if;
  end for;

  // Finding a totally positive generator for mm
  bool, a := IsNarrowlyPrincipal(mm);
  require bool : Sprintf("Ideal %o is not narrowly principal", IdealOneLine(mm));
  a := ReduceShintaniMinimizeTrace(a)[1];

  // Looping over all totally positive generators of the form au for u a totally positive unit mod squares
  Indexforsum := [];
  for u in TotallyPositiveUnits do
    Indexforsum cat:= [[b,a*u] : b in HalfOfCMExtensions(M,a*u)]; // Index for summation
  end for;

  return Indexforsum;
end intrinsic;



///////////// ModFrmHilD: Trace Formula ////////////////


/* Todos

* Correction factor when computing on the space k = (2,..,2) and chi = 1
* Test nontrivial characters.
* Test nonparallel weight and odd degree weight.
* Cubic fields.

FIXME
* Large weight is off

Notes

* Computing unit index and class groups. The big bottleneck is precomputing the
class numbers #CL(K) and Hasse unit index [ZK^* : ZF^*] for lots of CM-extensions K/F.
I have some code to quickly compute the Hasse unit index without doing the class group.

 */

intrinsic Trace(Mk::ModFrmHilD, mm::RngOrdIdl) -> Any
  {Computes the trace}
  if IsZero(mm) then
    return 0;
  elif IsNarrowlyPrincipal(mm) eq false then
    return 0;
  else
  // Space Preliminaries
  M := Parent(Mk);
  NN := Level(Mk);
  k := Weight(Mk);

  // Field Preliminaries
  F := BaseField(Mk);
  ZF := Integers(Mk);
  n := Degree(F);
  places := Places(M);
  P<x> := PolynomialRing(ZF);

  // Units and class group
  UF, mUF := UnitGroup(ZF);
  SetClassGroupBounds("GRH"); // I'm OK without a proof!

  // Index 
  Indexforsum := IndexOfSummation(Mk, mm);

  // Computation of summation
  Sumterm := 0;
  for pair in Indexforsum do

    // preliminaries
    b := pair[1];
    a := pair[2];
    D := b^2-4*a;

    // Asserts: Check that extension is CM
    require IsTotallyPositive(-(b^2-4*a)): "Non CM-extension in summation";

    // For each D = b^2-4*a, we create the quadratic field K = F(sqrt(d)) and store several quantities here

    // Create the quadratic field
    K := ext<F | x^2 - D >;
    ZK := Integers(K);

    // Class groups and units —— Magma requires absolute field
    Kabs := AbsoluteField(K);
    ZKabs := Integers(Kabs);
    h := ClassNumber(Kabs);

    // Unit Index:   w := 2*[ZK:ZF],
    // Map units in ZF -> ZK -> ZKabs and then check index [ZK:ZF]
    UK,mUK := UnitGroup(ZKabs);
    _, mKabstoK := IsIsomorphic(Kabs,K);
    q := #quo< UK | [(mKabstoK(mUF(u)))@@mUK : u in Generators(UF)] >;
    w := 2*q;
    /* When #Cl^+(F) = 1, then w is equal to the torsion subgroups of the unity group (roots of unity).
    This can be check with the following code.
    w := #TorsionUnitGroup(Kabs);
    require 2*q eq w: "Unit indices are off!";
    */

    //Weightfactor
    Weightfactor := function(a,b,l)
      _<x> := PowerSeriesRing(RealField(k[1]+20),k[1]+20); // extend with weight
      P := 1/(1 + a*x + b*x^2);
      return Coefficient(P,l);
    end function;

    // We now factor D = df^2
    DD := Discriminant(ZK); // Discriminant
    //_, d := IsNarrowlyPrincipal(DD); // Discriminant element 
    ff := Sqrt((D*ZF)/DD); // Conductor

    // Artin Symbol — this should be the same as QuadraticCharacter(F!d)! but does not create a ray class group
    function ArtinSymbol(pp)
      if IsSplit(pp,ZK) then return 1;
      elif IsRamified(pp,ZK) then return 0;
      else return -1; end if;
    end function;

    /* Let S_ff be the order of discriminant D = d*ff^2. We now need to
    loop over the orders ZK < S < S_ff and compute class number and embedding numbers
    The are indexed by conductors —— i.e. S = S_f where f | ff */

    // Constant in front of the conductor sum
    C := (h/w)*(&*[Weightfactor(Evaluate(b,places[i]),Evaluate(a,places[i]),k[i]-2) : i in [1..n]]);

    // Loop over the possible conductors with optimal embedding numbers
    conductorsum := 0;
    for aa in Divisors(ff) do // Loop over conductors.
      // Preliminaries
      term := 1;
      // First do contribution from class number of S —— note that h = Cl(K) has been pulled out of sum
      term *:= Norm(aa)*(&*([1] cat [1-ArtinSymbol(pp[1])*Norm(pp[1])^(-1) : pp in Factorization(aa)]));
      // Second do contribution from embedding numbers
      for pp in Factorization(NN) do
        // Preliminaries
        pi := UniformizingElement(pp[1]);
        vaa := Valuation(aa,pp[1]);
        b0,a0 := PolynomialMaximalOrder(b,a,ZF,pp[1]);
        a1 := a0*pi^(2*vaa);
        b1 := b0*pi^(vaa);
        /* By switching x^2 + b*x - a  -> x^2 + b1*x - a1 then
        the local discriminant changes by a factor of pi^(2*vaa)
        // Multiply by embedding numbers */
        term *:= EmbeddingNumbers(b1,a1,pp[1],pp[2]);
      end for;
      // Third add to the summation over all conductors
      conductorsum +:= term;
    end for;

    // Multiply Constant in front of the sum with the sum
    C *:= conductorsum;
    //print C;
    // Conclude by adding to overall summation
    Sumterm +:= C;
  end for;

  Constantterm := ConstantTerm(Mk,mm);
  tr := Constantterm + Sumterm;
  // print Constantterm, Sumterm, Round(tr);
  return Round(tr);

  end if;
end intrinsic;



///////////////////////////////////////////////////
//                                               //
//             Speed Trace Formula               //
//                                               //
///////////////////////////////////////////////////


//////////////////// Main function: Trace /////////////////////////

intrinsic STrace(Mk::ModFrmHilD, mm::RngOrdIdl) -> Any
  {Computes the trace}
  if IsZero(mm) then
    return 0;
  elif IsNarrowlyPrincipal(mm) eq false then
    return 0;
  else
  // Space Preliminaries
  M := Parent(Mk);
  NN := Level(Mk);
  k := Weight(Mk);

  // Field Preliminaries
  F := BaseField(Mk);
  ZF := Integers(Mk);
  n := Degree(F);
  places := Places(M);
  P<x> := PolynomialRing(ZF);

  // Index
  Indexforsum := TracePrecomputation(M)[mm];

  // Computation of summation
  Sumterm := 0;
  for StoredData in Indexforsum do

    // preliminaries
    b := StoredData[1];
    a := StoredData[2]; // x^2 + bx + a
    ZK := StoredData[5]; // Used for Artin Symbol
    ff := StoredData[6]; // Conductor
    h := StoredData[7]; // Class number of quadratic extension K/F
    w := StoredData[8]; // Unit index of quadratic extension K/F

    //Weightfactor
    Weightfactor := function(a,b,l)
      _<x> := PowerSeriesRing(RealField(),k[1]+20); // extend with weight
      P := 1/(1 + a*x + b*x^2);
      return Coefficient(P,l);
    end function;

    // Artin Symbol — this should be the same as QuadraticCharacter(F!d)! but does not create a ray class group
    function ArtinSymbol(pp)
      if IsSplit(pp,ZK) then return 1;
      elif IsRamified(pp,ZK) then return 0;
      else return -1; end if;
    end function;

    // Constant in front of the conductor sum
    C := (h/w)*(&*[Weightfactor(Evaluate(b,places[i]),Evaluate(a,places[i]),k[i]-2) : i in [1..n]]);

    // Accounting for the difference between embedding number for polynomials x^2 - a and x^2 - b +a
    if b ne 0 then
      C *:= 2;
    end if;

    // Storage : Factorization of NN by [pp,e] where pp^e is the power of pp dividing NN.
    factNN := [pair : pair in Factorization(NN)];

    // Loop over the possible conductors with optimal embedding numbers
    conductorsum := 0;
    for aa in Divisors(ff) do // Loop over conductors.
      // Preliminaries
      term := 1;
      // First do contribution from class number of S —— note that h = Cl(K) has been pulled out of sum
      term *:= Norm(aa)*(&*([1] cat [1-ArtinSymbol(pp[1])*Norm(pp[1])^(-1) : pp in Factorization(aa)]));
      // Second do contribution from embedding numbers
      for pair in factNN do
        // Preliminaries
        pp := pair[1]; // pp | NN
        e := pair[2]; // pp^e | NN
        f := Valuation(aa,pp); // Local conductor at pp where globally DD = dd*aa^2
        g := Valuation(Discriminant(ZK),pp); // Local power of pp in the discriminant dd where DD  = dd*aa^2
        // Multiply by embedding numbers
        term *:= OptimalEmbeddings(e,2*f,g,pp,ZK);
      end for;
      // Third add to the summation over all conductors
      conductorsum +:= term;
    end for;

    // Multiply Constant in front of the sum with the sum
    C *:= conductorsum;
    // Conclude by adding to overall summation
    Sumterm +:= C;
  end for;

  Constantterm := ConstantTerm(Mk,mm);
  tr := Constantterm + Sumterm;

  return Round(tr);
  end if;
end intrinsic;



///////////////////////////////////////////////////
//                                               //
//             Embedding Numbers                 //
//                                               //
///////////////////////////////////////////////////


//////////////////////////// Optimal Embeddings — Main ///////////////////////////

intrinsic OptimalEmbeddings(e::RngIntElt, f::RngIntElt, g::RngIntElt, pp::RngOrdIdl, ZK::RngOrd) -> RngIntElt
  {Returns all solutions to x^2+nx+m mod pp^e}

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


//////////////////////////// Optimal Embeddings — Odd ////////////////////////////////

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
    N := q^(f/2)*ArtinSymbol(pp)*(1 + ArtinSymbol(pp));
  end if;
  return N;
end intrinsic;


//////////////////////////// Optimal Embeddings — Even ////////////////////////////////

intrinsic OptimalEmbeddingsEven(e::RngIntElt, f::RngIntElt, g::RngIntElt, pp::RngOrdIdl, ZK::RngOrd) -> RngIntElt
  {Returns all solutions to x^2 - D mod pp^e where D = d*pi^(g+f)}

  // Size of residue field
  q := Norm(pp);

  // Valuation of 2*ZF
  ZF := Order(pp);
  v := Valuation(2*ZF,pp);

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
        N := q^(f/2)*ArtinSymbol(pp)*(1 + ArtinSymbol(pp));
      end if;
    end if;
  end if;
  return N;
end intrinsic;





///////////////////////////////////////////////////
//                                               //
//           Embedding Numbers  (Old)            //
//                                               //
///////////////////////////////////////////////////

//////////////////////////// Optimal Embeddings — Alternative Method (Old) ///////////////////////////////
/* Computes the number of optimal embeddings of a local order defined by a polynomial
x^2 + nx + m into and Eichler order of level pp^e  */

intrinsic EmbeddingNumbers(n::RngOrdElt, m::RngOrdElt, pp::RngOrdIdl, e::RngIntElt) -> Any
  {Returns the optimal embeddings of x^2+nx+m into an order of level pp^e}
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


//////////////////////////// Polynomial of a maximal order in a Local Algebra ///////////////////////////////

/* Let K/F be a quadratic algebra over F (not necessarily a field, possibly F+F).
This computes a minimal polynomial of the form x^2+nx+m for the maximal order in F. Returns just n,m
This is used for the conductor sum, as once we have the minimal polynomial it is easy
to produce polynomials for other orders of higher level.*/
intrinsic PolynomialMaximalOrder(n::RngOrdElt, m::RngOrdElt, ZF::RngOrd, pp::RngOrdIdl) -> Any
  {Returns n,m for polynomial x^2 + nx + m which generates the maximal order}
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
      // Case 1.1.1: Local algebra F_2 is split or inert. Return x^2 + x + 1
      if IsSplit(pp) then
        n0 := ZF ! -1;
        m0 := ZF ! -4;
      elif IsInert(pp) then
        n0 := ZF ! 1;
        m0 := ZF ! -1;
      /* Case 1.1.2: Local algebra F_2 is inert or ramified (extension of Q2)
      Find an equivalent quadratic extension of Q2 and use minimal polynomial for ring of integers. */
      else
        for d in { 1, 2, 5, 6, 10, 14 } do
          L := ext< F | x^2 + d >;
          ZL := Integers(L);
          ppl := pp * ( 1 * ZL );
          if #Factorization(ppl) eq 2 then
            Q := QuadraticField( -Discriminant(F) * d );
            poly := MinimalPolynomial(Integers(Q).2);
            // print poly, d, -Discriminant(F);
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






///////////////////////////////////////////////////
//                                               //
//       Class Groups and Units Indices          //
//                                               //
///////////////////////////////////////////////////


//////////////////////////// Hasse Unit Index and Class Groups ////////////////////////////////

intrinsic ClassGroupandUnitIndex(M::ModFrmHilDGRng, K::FldNum, D::RngQuadElt, ZF::RngQuad, hplus::RngIntElt) -> Any
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
      //B := 2 + zeta_2 + zeta_2^(-1); // this is the norm from K to F — should be equivalent to 1 + zeta_2 + 1/zeta_2
      //print "hey", oddpartw, power, w;
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
//          Takase Trace Formula (old)           //
//                                               //
///////////////////////////////////////////////////

//////////////////// Preliminary function /////////////////////////

/*
I'm having type issues with switching from quadratic fields to higher degree.
Apparently the Type RngOrdElt is not a subset of FldOrdElt. For quadratic fields
elements of ZF are of Type RngOrdElt but for cubic fields they are of type FldOrdElt.
Edgar: use RngElt
*/


/*

// Overloaded. The other quadratic character computes the ray class group!
// This is a lot faster but needs a fundamental discriminant.
intrinsic QuadraticCharacter(D::RngOrdElt,pp::RngOrdIdl) -> RngIntElt
  {Returns the value of the quadratic character chi_D(pp). D must be a fundamental discriminant!}
  ZF := Parent(D);
  F := FieldOfFractions(ZF);
  // Odd primes : Legendre Symbol (D/pp)
  if Valuation(ideal<ZF|2>,pp) eq 0 then
    return LegendreSymbol(D,pp);
  // Even primes : Use Hilbert Symbol
  else
    if D*ZF subset pp then // To contain = To divide
      return 0;
    else
      pi := SafeUniformizer(pp);
      return HilbertSymbol(F!D,pi,pp);
    end if;
  end if;
end intrinsic;
*/

///////////// ModFrmHilD: Trace Formula Takase ////////////////

/*

intrinsic Trace(Mk::ModFrmHilD, mm::RngOrdIdl) -> SeqEnum[ModFrmHilDElt]
  { returns the trace of the m^th Hecke operate on S_k(NN)}
  // Attributes
  M := Parent(Mk);
  NN := Level(Mk);
  k := Weight(Mk);
  chi := Character(Mk);
  F := BaseField(Mk);
  ZF := Integers(Mk);
  n := Degree(F);
  places := Places(M);
  Disc := Discriminant(Integers(F));
  DedekindZetatwo := DedekindZetatwo(M); // No precision set
  R := RealField(); // No precision set
  // Return 0 when mm = 0
  if mm eq 0*ZF then
    return 0;
  else
  // Requirements
  require forall{ki : ki in k | ki gt 2}: "Weights must all be greater than than 2";
  require Gcd(NN,mm) eq 1*ZF: "Level and ideal for Hecke operator must be coprime";
  // First term A(NN)
  C0 := 2*DedekindZetatwo/(2*Pi(R))^(2*n); // Product is broken up into several steps
  C0 *:= Disc^(2)*Norm(NN)/Sqrt(Disc);
  C0 *:= &*[i-1 : i in k];
  C0 *:= &*([1] cat [1+Norm(p[1])^(-1) : p in Factorization(NN)]);
  // Second term BB(NN,mm)
  // Subfuction c(a,b)
  c := function(a,b,l)
    _<x> := PowerSeriesRing(R);
    P := 1/(1 + a*x + b*x^2);
    return Coefficient(P,l);
  end function;
  // Subfuction d(a,b)
  d := function(a,b,aa)
    Q,mQ := quo< ZF | aa >;
    T := [t@@mQ : t in Q | (t^2 + mQ(b)*t + mQ(a)) eq mQ(0) ];
    if #T eq 0 then
      return 0; // List is empty;
    else
      _,gen := IsPrincipal(aa);
      if 0 in T then // replace 0 => generator
        T := [gen] cat [t : t in T | t ne 0];
      end if;
      return &+[chi(t) : t in T];
    end if;
  end function;
  // Preliminaries
  a := IdealToShintaniRepresentative(M,1*ZF,mm);
  _<x> := PolynomialRing(F);
  SetClassGroupBounds("GRH"); // I'm OK without a proof!
  Indexforsum := CMExtensions(M,a); // Index for summation
  // Actual summation
  C1 := 0;
  for b in Indexforsum do
    D := b^2-4*a;
    K := ext<F | x^2 - D >;
    ZK := Integers(K);
    DD := Discriminant(ZK);
    // Class group/Characters computations.
    L := AbsoluteField(K); // Class groups/Units computations only for absolute extensions?
    h := ClassNumber(L);
    w := #TorsionUnitGroup(L);
    chi_K := QuadraticCharacter(F!D);
    // Indices for more sums
    cc := Sqrt((D*ZF)/DD); // D*ZF = DD*cc^2 with DD a fundamental discriminant
    cc00 := 1*ZF;
    for pp in Factorization(cc) do
      if Valuation(NN,pp[1]) eq 0 then
        cc00 *:= pp[1]^pp[2];
      end if;
    end for;
    cc11 := 1*ZF;
    for pp in Factorization(NN) do
      vp := Valuation(cc,pp[1]);
      cc11 *:= pp[1]^(Max(2*vp+1,pp[2]+vp));
    end for;
    // Second term C2
    C2 := h/w * Norm((NN*cc)/(cc00*cc11));
    C2 *:= &*[ Evaluate(a,places[i])^(1-k[i])*c(Evaluate(b,places[i]),Evaluate(a,places[i]),k[i]-2) : i in [1..n]];
    //First sum
    D0 := 0;
    for aa in Divisors(cc00) do
      D1 := Norm(aa);
      D1 *:= &*([1] cat [1-chi_K(pp[1])*Norm(pp[1])^(-1) : pp in Factorization(aa)]);
      D0 +:= D1;
    end for;
    C2 *:= D0;
    //Second sum
    E0 := 0;
    //for aa in Divisors(cc11/NN) do
    for aa in Divisors(cc11/NN) do
      E1 := d(a,b,cc11/aa)*Norm(aa);
      E1 *:= &*[ Evaluate(a,places[i])^(Integers()!(k[i])/2) : i in [1..n]]; // This last part needs to be fixed for signs of Hecke characters
      E1 *:= &*([1] cat [1-chi_K(pp[1])*Norm(pp[1])^(-1) : pp in Factorization(aa)]);
      E0 +:= E1;
    end for;
    C2 *:= E0;
    // Now adding C2 to the total sum
    C1 +:= C2;
  end for;
  // Square root of character
  sqrtchi := function(mm)
    if IsSquare(mm) then
      _,mm0 := IsSquare(mm);
      return chi(mm0);
    else
      return 0;
    end if;
  end function;
  FinalTrace := C0*sqrtchi(mm) + (-1)^n*C1;
  // The equation is off by a little bit. We need to add this correction factor.
  CorrectionFactor := Norm(a)^(Integers()!(k[1]/2-1));
  //print FinalTrace*CorrectionFactor;
  return Round(FinalTrace*CorrectionFactor);
  end if;
end intrinsic;

*/

///////////// ModFrmHilD: Trace Formula w/ precomputations ////////////////

/*

// Overloaded for Ideal and Shintani Rep
intrinsic TracePrecomputation(Mk::ModFrmHilD, mm::RngOrdIdl) -> SeqEnum[ModFrmHilDElt]
  { returns the trace of the m^th Hecke operate on S_k(NN)}
  M := Parent(Mk);
  ZF := Integers(Mk);
  a := IdealToShintaniRepresentative(M,1*ZF,mm);
  return TracePrecomputation(Mk,a);
end intrinsic



intrinsic TracePrecomputation(Mk::ModFrmHilD, a::RngOrdElt) -> SeqEnum[ModFrmHilDElt]
  { Let (a) = mm be totally positive generator. This returns the trace of the m^th Hecke operate on S_k(NN)}
  // Attributes
  M := Parent(Mk);
  NN := Level(Mk);
  k := Weight(Mk);
  chi := Character(Mk);
  F := BaseField(Mk);
  ZF := Integers(Mk);
  n := Degree(F);
  mm := a*ZF;
  places := Places(M);
  Disc := Discriminant(Integers(F));
  DedekindZetatwo := DedekindZetatwo(M); // No precision set
  R := RealField(); // No precision set
  // Return 0 when a = 0
  if a eq 0 then
    return 0;
  else
  // Requirements
  require forall{ki : ki in k | ki gt 2}: "Weights must all be greater than than 2";
  require Gcd(NN,mm) eq 1*ZF: "Level and ideal for Hecke operator must be coprime";
  // First term A(NN)
  C0 := 2*DedekindZetatwo/(2*Pi(R))^(2*n); // Product is broken up into several steps
  C0 *:= Disc^(2)*Norm(NN)/Sqrt(Disc);
  C0 *:= &*[i-1 : i in k];
  C0 *:= &*([1] cat [1+Norm(p[1])^(-1) : p in Factorization(NN)]);
  // Second term BB(NN,mm)
  // Subfuction c(a,b)
  c := function(ai,bi,l)
    _<x> := PowerSeriesRing(R);
    P := 1/(1 + ai*x + bi*x^2);
    return Coefficient(P,l);
  end function;
  // Subfuction d(a,b)
  d := function(a,b,aa)
    Q,mQ := quo< ZF | aa >;
    T1 := [ (t^2 + mQ(b)*t + mQ(a)) : t in Q ];
    T := [t@@mQ : t in Q | (t^2 + mQ(b)*t + mQ(a)) eq mQ(0) ];
    if #T eq 0 then
      return 0; // List is empty;
    else
      _,gen := IsPrincipal(aa);
      if 0 in T then // replace 0 => generator
        T := [gen] cat [t : t in T | t ne 0];
      end if;
      return &+[chi(t) : t in T];
    end if;
  end function;
  // Preliminaries
  Indexforsum := HMFPrecomputation(M)[a]; // Index for summation
  // Actual summation
  C1 := 0;
  for StoredData in Indexforsum do
    b := StoredData[1];
    D := StoredData[2];
    FundD := StoredData[3];
    cc := StoredData[4];
    h := StoredData[5];
    w := StoredData[6];
    cc00 := 1*ZF;
    for pp in Factorization(cc) do
      if Valuation(NN,pp[1]) eq 0 then
        cc00 *:= pp[1]^pp[2];
      end if;
    end for;
    cc11 := 1*ZF;
    for pp in Factorization(NN) do
      vp := Valuation(cc,pp[1]);
      cc11 *:= pp[1]^(Max(2*vp+1,pp[2]+vp));
    end for;
    // Second term C2
    C2 := h/w * Norm((NN*cc)/(cc00*cc11));
    C2 *:= &*[ Evaluate(a,places[i])^(1-k[i])*c(Evaluate(b,places[i]),Evaluate(a,places[i]),k[i]-2) : i in [1..n]];
    //First sum
    D0 := 0;
    for aa in Divisors(cc00) do
      D1 := Norm(aa);
      D1 *:= &*([1] cat [1-QuadraticCharacter(FundD,pp[1])*Norm(pp[1])^(-1) : pp in Factorization(aa)]);
      D0 +:= D1;
    end for;
    C2 *:= D0;
    //Second sum
    E0 := 0;
      for aa in Divisors(cc11/Gcd(NN,cc11)) do
        E1 := d(a,b,cc11/aa)*Norm(aa);
        E1 *:= &*[ Evaluate(a,places[i])^(Integers()!(k[i])/2) : i in [1..n]]; // This last part needs to be fixed for signs of Hecke characters
        E1 *:= &*([1] cat [1-QuadraticCharacter(FundD,pp[1])*Norm(pp[1])^(-1) : pp in Factorization(aa)]);
        E0 +:= E1;
      end for;
      C2 *:= E0;
    // Now adding C2 to the total sum
    C1 +:= C2;
  end for;
  // Square root of character
  sqrtchi := function(mm)
    if IsSquare(mm) then
      _,mm0 := IsSquare(mm);
      return chi(mm0);
    else
      return 0;
    end if;
  end function;
  FinalTrace := C0*sqrtchi(mm) + (-1)^n*C1;
  // The equation is off by a little bit. We need to add this correction factor.
  CorrectionFactor := Norm(a)^(Integers()!(k[1]/2-1));
  return Round(FinalTrace*CorrectionFactor);
  end if;
end intrinsic;
*/

////////////////// Future Trace Work ////////////////////

//Correction Factor: exists ki = 2
/*
ConstantFactor := 0;
if exists{ki : ki in k | ki eq 2} then
  if IsTrivial(chi) then
    ConstantFactor := &+[Norm(aa) : aa in Divisors(mm) | Norm(GCD(mm/aa,NN)) eq 1];
  end if;
end if;
*/




//////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////
//                                               //
//                    Extras                     //
//                                               //
///////////////////////////////////////////////////


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
  require Norm(Level(Mk)) eq 1: "Only implemented in trivial level";
  N := Newforms(Mk);
  if #N eq 0 then
    return HMFZero(Mk);
  else
    return &+[NewformTrace(i) : i in N];
  end if;
end intrinsic;


/*
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
