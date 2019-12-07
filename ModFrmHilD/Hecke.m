///////////////////////////////////////////////////
//                                               //
//                Hecke Operators                //
//                                               //
///////////////////////////////////////////////////

///////////// ModFrmHilDElt: Hecke Operators ////////////////

 intrinsic HeckeOperator(f::ModFrmHilDElt, nn::RngOrdIdl) -> ModFrmHilDElt
   {returns T(n)(f) for the trivial character}
   return HeckeOperator(f, nn, HeckeCharacterGroup(Level(f))! 1);
 end intrinsic;


 intrinsic HeckeOperator(f::ModFrmHilDElt, nn::RngOrdIdl, chi::GrpHeckeElt) -> ModFrmHilDElt
   {returns associative array with coefficients for T(nn)(f) with loss of precision.}
   Mk := Parent(f);
   M :=Parent(Mk);
   F:=BaseField(M);
   ZF:=Integers(F);
   k0 := Max(Weight(f));
   //We work in smaller precision and obtain a function the space of precision Prec/Norm(nn)
   coeffsTnnf := AssociativeArray();
   newPrec:=0;
   for bb in NarrowClassGroupReps(M) do 
    coeffsTnnf[bb] := AssociativeArray();
    end for;
   precisionReached:=false; // keeps track if we have reached the precision for T(nn)(f)
    //Now we loop through each trace
   for T:=0 to Precision(M) do
    traceDefined:=0; //keeps track if coefficients for all ideals of a given trace are defined 
    totalIdealsByTrace:=0;
    for bb in  NarrowClassGroupReps(M) do
      IdealsTraceT:=ShintaniRepsByTrace(M)[bb][T]; //get list of Shintani reps with trace T
      totalIdealsByTrace+:= #IdealsTraceT;
      for x in IdealsTraceT do
        I:=x*bb^(-1);
        c :=0;
        allDivisors:=true; //keeps track if all the coefficients in the sum for an ideal are defined
        // loop over divisors
        // Formula 2.23 in Shimura - The Special Values of the zeta functions associated with Hilbert Modular Forms
        for aa in Divisors(ZF!!(I + nn)) do
          if aa^(-2) * (I* nn) notin AllIdeals(M) then
           allDivisors:=false ; break; //stop looping through divisors if coefficient for at least one divisor is not defined ( if trace (aa^(-2) * (I* nn)) is greater than precision)
             else
              if I eq 0*ZF then c+:= chi(aa) * Norm(aa)^(k0 - 1) * Coefficients(f)[bb][I]; //takes care if the coefficients for the zero ideal are different
                else c+:= chi(aa) * Norm(aa)^(k0 - 1) * Coefficient(f, ZF !! (aa^(-2) * (I* nn)));
                end if;
             end if;
          end for;
        if allDivisors eq true then  //if T(nn)(f)[I] is defined, give a value
          traceDefined +:= 1;
          coeffsTnnf[bb][I] := c;
         else 
         coeffsTnnf[bb][I] := 0;
         //break; //stop looping thorough ideals of given trace T if T(nn)(f)[I] is not defined for some ideal I with trace T
         end if;
        end for;
      end for;
    if (traceDefined eq totalIdealsByTrace) and (precisionReached eq false) then 
      newPrec:=T;
      else 
        newPrec:=Max(0, newPrec);
        precisionReached:= true;
        for bb in NarrowClassGroupReps(M) do
           IdealsTraceT:=ShintaniRepsByTrace(M)[bb][T];
           for x in IdealsTraceT do
            I:=x*bb^(-1);
            if I in Keys(coeffsTnnf[bb]) then
              coeffsTnnf[bb][I]:=0;
              end if;
            end for;
           end for;
      end if;
    end for;
  //return coeffsTnnf, newPrec;
    g:=HMF(Mk, coeffsTnnf);
    g`Precision:=newPrec;
  return g;      
 end intrinsic;



///////////////////////////////////////////////////
//                                               //
//                 Trace Formula                 //
//                                               //
///////////////////////////////////////////////////

//////////////////// Preliminary function /////////////////////////

/*
I'm having type issues with switching from quadratic fields to higher degree. 
Apparently the Type RngOrdElt is not a subset of FldOrdElt. For quadratic fields 
elements of ZF are of Type RngOrdElt but for cubic fields they are of type FldOrdElt.
*/


// Computes all CM-Quadratic fields needed for computation
intrinsic CMExtensions(M::ModFrmHilDGRng,a::RngOrdElt) -> SeqEnum
  {Computes all elements b satifying b^2 << 4a}
  F := BaseField(M);
  ZF := Integers(M);
  places := places(M);
  /*
  Every element b^2 << 4a satifies |b| < 2sqrt(a). 
  This is a square centered at the origin. We will enumerate half of it.
  */
  XLB := -2*Sqrt(Evaluate(a,places[1])); // XLB = X lower bound
  YLB := 0;
  XUB := 2*Sqrt(Evaluate(a,places[1]));
  YUB := 2*Sqrt(Evaluate(a,places[2]));
  T := BoundedRepresentatives(M,1*ZF,XLB,YLB,XUB,YUB);
  T := [ i : i in T | i^2-4*a ne 0]; // Zero is "technically" not totally positive for this computation
  T cat:= [-i : i in T | i ne 0];
  return T;
end intrinsic;


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


///////////// ModFrmHilD: Trace Formula ////////////////

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
  places := places(M);
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



///////////// ModFrmHilD: Trace Formula w/ precomputations ////////////////


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
  places := places(M);
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
    h := StoredData[3];
    w := StoredData[4];
    FundD := StoredData[5];
    cc := StoredData[6];
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


///////////////////////////////////////////////////
//                                               //
//                Hecke stability                //
//                                               //
///////////////////////////////////////////////////


//Given what space M of Hilbert Modular Forms I should be looking at, and what level
//Given an Eisenstein series E of weight kE and a weight kS of cusp forms that I want to generate
//Given a collection P of primes for Hecke operators I want to look at
//Computes a basis L for S_{kS + kE}
//Compute LE = [f/E :  f is in L]
//For each p in P and each g in LE, compute T_p g.
//Then check if T_p g is in the span of LE
//If it is not, delete g from LE
//Returns LE

//intrinsic Intersection(Spaces::SeqEnum[SeqEnum[ModFrmHilDElt]]) -> SeqEnum[ModFrmHilDElt]
intrinsic Intersection(Spaces::List) -> List
  {Given a list of bases for spaces of forms, find a basis for the intersection of those spaces}
  //Assuming all forms are living in the same spaces, returns parameters associated to them
  M := Parent(Spaces[1][1]);
  N := Level(Spaces[1][1]);
  k := Weight(Spaces[1][1]);
  F := BaseField(M);
  //Outputs the coefficients of the forms in forms
  A := [[Coefficients(f) : f in Space] : Space in Spaces];
  V := VectorSpace(F, #A[1][1]);
  //Coercing A to live in V, and converting my basis to the vector space it spans
  A1 := [sub<V | [V ! f : f in Space] > : Space in A];
  //The intersection of all the spaces in A1
  intersection := &meet A1;
  B := Basis(intersection);
  return [*HMF(M,N,k,Eltseq(b)) : b in B*]; //We want to take the intersection of the spaces in A1
  //Converts W back to Hilbert modular forms
end intrinsic;

//k is the weight of cusp forms we want to generate, and eta and psi are the characters we want associated to them
//ke is the weight of the eisenstein series we want to work with
intrinsic HeckeStability(M::ModFrmHilD, N::RngOrdIdl, k::SeqEnum[RngIntElt]) -> SeqEnum[ModFrmHilDElt], RngIntElt
  { returns a Basis for weight k cusp forms}
  //We need our eisenstein series
  //There is no particular reason to make ke be 1--but it works, probably
  ke := [2,2];
  H := HeckeCharacterGroup(N);
  //If #H = 1 then E doesn't work down below. But that's the case we are in here
  //There's no particular reason to make these characters trivial--but they work.
  //All eisenstein series we are using as candidates
  E := [EisensteinSeries(M, N, eta, H!1, ke) : eta in Elements(H)]; // | eta ne H!1 ];
  assert E ne [];
  assert #k eq #ke;
  ks := [ke[i] + k[i] : i in [1..#Weight(E[1])] ];
  CB := CuspFormBasis(M, N, ks);
  assert CB ne [];
  BaseCandidates := [* [* c/e : c in CB *] : e in E *];
  //Quotients of CB by E, which will span the cusp forms in weight k.
  //Candidates should be the intersection of the BaseCandidate spaces
  Candidates := Intersection(BaseCandidates);
  return Candidates;
  //Ideals that index the Hecke operators that we will be applying to our forms. We want prime ideals of small norm
  //IdealBound is how far out we go in generating our prime ideals. I really have no idea what this should be
  IdealBound := Precision(M) div 20;
  Ideals := PrimesUpTo(IdealBound,BaseField(M));
  print Ideals;
  //What we get when we apply our Hecke operators to the things in BaseCandidates
  HeckeCandidates := [* [* HeckeOperator(Candidates[i], Ideals[j]) : i in [1..#Candidates] *] : j in [1..#Ideals] *];
  //We have a problem because when you apply Hecke operators, you get forms with different numbers of coefficients, and that is bad
  Basis := Intersection(HeckeCandidates);
  return Basis, #Basis;
end intrinsic;
