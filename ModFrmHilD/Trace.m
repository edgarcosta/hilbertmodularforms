
///////////////////////////////////////////////////
//                                               //
//                 Trace Formula                 //
//                                               //
///////////////////////////////////////////////////

//////////////////// Preliminary functions /////////////////////////

////////// General Functions ///////////////////

// Embedding Numbers 

/* Computes the number of optimal embeddings of a local order defined by a polynomial 
x^2 + nx + m into and Eichler order of level pp^e  */

// TODO: Is there a simple formula in terms of just the arithmetic of the field? John has one when pp is an "odd" prime. 

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



/* Let K/F be a quadratic algebra over F (not necessarily a field, possibly F+F). 
This computes a minimal polynomial of the form x^2+nx+m for the maximal oder in F. Returns just n,m
This is used for the conductor sum, as once we have the minimal polynomial it is easy 
to produce polynomials for other orders of higher level.*/

// Notes: this is super slow. 
intrinsic PolynomialMaximalOrder(n::RngOrdElt, m::RngOrdElt, ZF::RngOrd, pp::RngOrdIdl) -> Any
  {Returns n,m for polynomial x^2+nx+m which generates the maximal order}
  // Preliminaries
  D := n^2-4*m;
  F := FieldOfFractions(ZF);
  _<x> := PolynomialRing(ZF);
  K := ext< F | x^2-D >;
  ZK := Integers(K);
  qq := Factorization(pp*(1*ZK))[1][1]; // qq is the prime above pp
  /* Check if Split
    Yes: return x^2 - 1. not 2
         return use minimal polynomial of generator for ring of integers  
    No -> Check if x^2-D is ramified. 
      Yes: return unformizer. // Ramified
      No: return generator for ZF/pi. // Inert */
  if IsSplit(qq) then 
    if Norm(pp) mod 2 eq 0 then
      w := ZF.2; // This minimal polynomial of this element splits over F and it is maximal
      minpoly := MinimalPolynomial(w);
      coef := Coefficients(minpoly);
      n0 := coef[2];
      m0 := coef[1];
    else // Otherwise use 
      n0 := ZF!0;
      m0 := ZF!-1;
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



////////// Trace Specific Functions //////////////


// Constant Term

/* TODO 
* Nonparallel weight: We have Norm(mm)^(Integers()!(k[1]/2-1)) which should be m_i^(k_i/2-1). This comes from trace on weight space
* Character: The character is on the narrow class group of modulus NN where NN is the level, but
in magma this yeild 0 for ideals that are not comprime to the level and we need this to be 1. 
*/

// Returns the constant term for the trace formula
// Notes: No precision set which cause problems at high weight (k > 100)
intrinsic ConstantTermJV(Mk::ModFrmHilD, mm::RngOrdIdl) -> Any 
  {Constant term for JV Summation}
  // Preliminaries
  t := 0;
  if IsSquare(mm) then 
    _,sqrtmm := IsSquare(mm);
    if IsPrincipal(sqrtmm) then 
      t := 1;
    end if;
  end if;
  if t eq 1 then 
    // More preliminaries
    M := Parent(Mk);
    NN := Level(Mk);
    k := Weight(Mk);
    chi := Character(Mk);
    F := BaseField(Mk);
    ZF := Integers(Mk);
    n := Degree(F);
    places := places(M);
    Disc := Discriminant(ZF);
    h := ClassNumber(F); // This needs to be stored
    DedekindZetatwo := DedekindZetatwo(M); // No precision set 
    R := RealField(); // No precision set

    C0 := 2*DedekindZetatwo/(2*Pi(R))^(2*n); // Product is broken up into several steps
    C0 *:= h*Disc^(3/2)*Norm(NN); 
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
We don't really need this factor so I have turned this off for now.
*/ 

// Returns a correction factor when k = [2,2,..2] and trivial character chi = 1.
// Notes: Currently disabled 
intrinsic CorrectionFactorJV(Mk::ModFrmHilD, mm::RngOrdIdl) -> Any
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




// Index of Summation.

// TODO: We only need half of these terms since roots of x^2 + tx + nu and x^2 - tx + nu have the same weight factor. 

/* Returns representatives for all of the CM-extensions of the forms x^2 + tx + nu where n 
is totally positive generator for the fractional ideal representing the Hecke operator and 
u comes form a set of representative for the totally positive units modulo squares. 
*/
// Notes: None
intrinsic IndexOfSummationJV(Mk::ModFrmHilD, mm::RngOrdIdl) -> SeqEnum
  {Computes the a,b for which x^2-bx-a is used in the summation}
  // Preliminaries
  M := Parent(Mk);
  F := BaseField(Mk);
  ZF := Integers(Mk);

  // Computing totally positive units mod squares
  U,mU := UnitGroup(ZF);
  Ugens := [mU(u) : u in Generators(U)];
  TotallyPositiveUnits := [];
  /* 
  Every totally positive unit mod squares can be written as e = u_i^a_i where a_i = 0,1 and u_i are the generators for the unit group 
  We just loop over all combinations of generators and check to see if the resulting unit is totally positive. 
  */
  for v in CartesianPower([0,1],#Ugens) do
    unitelt := &*[Ugens[i]^v[i] : i in [1..#Ugens]];
    if IsTotallyPositive(unitelt) then
      Append(~TotallyPositiveUnits,unitelt);
    end if;
  end for;

  // Finding a totally positive generator for mm
  _,a := IsNarrowlyPrincipal(mm);
  a := ReduceShintaniMinimizeTrace(a);
  
  // Looping over all totally positive generators of the form au for u a totally positive unit mod squares
  Indexforsum := [];
  for u in TotallyPositiveUnits do 
    Indexforsum cat:= [[b,a*u] : b in CMExtensions(M,a*u)]; // Index for summation
  end for;

  return Indexforsum;
end intrinsic;


///////////// ModFrmHilD: Trace Formula ////////////////

// TODOs
/*

*** High Priority ***

* Embedding numbers is extremely slow — If we can express the embedding numbers in terms of the 
arithmetic of the field this will clean up code and greatly speed up computations. 
* Computing unit index and class groups. The big bottleneck is precomputing the 
class numbers #CL(K) and Hasse unit index [ZK^* : ZF^*] for lots of CM-extensions K/F. 
I have some code to quickly compute the Hasse unit index without doing the class group.  
* Test nontrivial characters.
* Test nonparallel weight and odd degree weight.
* Cubic fields.

*** Low Priority ***

* ConstantTermJV(Mk,mm) does not return a rational number. Can this be fixed? — This will fix precision errors at high weight. 


*/

intrinsic JVTrace(Mk::ModFrmHilD, mm::RngOrdIdl) -> Any
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
  places := places(M);  
  P<x> := PolynomialRing(ZF);

  // Units and class group
  UF,mUF := UnitGroup(ZF);
  SetClassGroupBounds("GRH"); // I'm OK without a proof!

  // Index
  Indexforsum := IndexOfSummationJV(Mk,mm);

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
      _<x> := PowerSeriesRing(RealField());
      P := 1/(1 + a*x + b*x^2);
      return Coefficient(P,l);
    end function; 

    // We now factor D = df^2 
    DD := Discriminant(ZK); // Discriminant
    _,d := IsPrincipal(DD); // Discriminant element
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

  Constantterm := ConstantTermJV(Mk,mm);
  tr := Constantterm + Sumterm;
  // print Constantterm, Sumterm, Round(tr);
  return Round(tr);

  /* Future work 
  We can add a correction factor to compute the actual trace when k = (2,..,2)
  Correctionfactor := CorrectionFactorJV(Mk,mm); // This isn't returning a number in Q
  tr := Constantterm + Sumterm + Correctionfactor;
  */
  
  end if;
end intrinsic;



//////////////////////  Computing Trace Forms ////////////////////////////////////


// Trace Form 
intrinsic JVTraceForm(Mk::ModFrmHilD) -> ModFrmHilDElt
  {Creates the trace form in the space Mk}
  M := Parent(Mk);
  Q := Rationals();
  bbs := NarrowClassGroupReps(M);
  coeffs := AssociativeArray(bbs);
  for bb in bbs do
    coeffs[bb] := AssociativeArray();
    for I in IdealsByNarrowClassGroup(M)[bb] do
      coeffs[bb][I] := Q!JVTrace(Mk,I);
    end for;
  end for;
  elt := HMF(Mk, coeffs);
  return elt;
end intrinsic;



/////////////// ModFrmHilD: Trace Formula w/ precomputations ////////////////
















//////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////
//                                               //
//                    Extras                     //
//                                               //
///////////////////////////////////////////////////



// Hasse Unit Index. 
intrinsic ClassGroupandUnitIndex(K::FldNum, D::RngQuadElt, ZF::RngQuad, hplus::RngIntElt) -> Any
  {Returns the unit index 2[Z_K^* : Z_F^*] = #mu_K [Z_K^* : mu_K Z_F^*] and the narrow class number}
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
    if h mod 4 eq 2 then 
      B := D;
    else
      // We now create a generator for mu_K(2) the 2-power roots of unity
      g := mu_K.1;
      twopower := 2^Valuation(w,2);
      power := Integers()!(w/twopower);
      zeta_2 := mKabs(mapmu_K(g)^power); // zeta_2 is now an element of a CM-extension K/F 
      B := Norm(1+zeta_2); // this is the norm from K to F — should be equivalent to 1 + zeta_2 + 1/zeta_2
    end if;

    // the factor 2 comes into play only when B*ZF = aa^2 and aa is principal
    issquare, aa := IsSquare(B*ZF);
    if issquare eq true then
      if IsPrincipal(aa) then
        unitindex *:= 2;
      end if;
    end if;

  end if; ////////// 

  // return
  return h, unitindex;
end intrinsic;


intrinsic NewformTrace(f::ModFrmHilDElt) -> ModFrmHilDElt
  {returns the full Galois orbit of a modular form over Q}
  fSpace := Parent(f);
  M := Parent(fSpace);
  k := Weight(fSpace);
  require k ne 2: "Only inmplemented when k =/= 2";
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
  return &+[NewformTrace(i) : i in NewformsToHMF(Mk)];
end intrinsic;








/// The 

intrinsic TwoLinearDependence(List::SeqEnum[ModFrmHilDElt]) -> SeqEnum[RngIntElt]
  {finds a small non-trivial integral linear combination between components of v away from nn. If none can be found return 0.}
  M := GradedRing(List[1]);
  ZF := Integers(M);
  bbs := NarrowClassGroupReps(M);
  CoeffLists := [[] : i in [1..#List]];
  for bb in bbs do
    for nn in IdealsByNarrowClassGroup(M)[bb] do
      if nn ne 0*ZF then
        for i in [1..#List] do
          Append(~CoeffLists[i], Coefficients(List[i])[bb][nn]);
        end for;
      end if;
    end for;
  end for;
  return LinearDependence(CoeffLists);
end intrinsic;








