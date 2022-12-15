////////////////////////////////////////////////////////////////////////////////
//
//     EllipticPoints.m
//
// Functionality for computing the number and types of elliptic points.
//
////////////////////////////////////////////////////////////////////////////////

// Types, Records, and Constants.
OrderTermRecordFormat := recformat<Order, Conductor, PicardNumber, HasseUnitIndex>;


////////////////////////////////////////////////////////////////////////////////
//
// Helper functions.
//
////////////////////////////////////////////////////////////////////////////////

intrinsic TotallyPositiveUnitsModSquaresRepresentatives(UF, mUF) -> Any
{}
    // UF  -- Unit group of ground field F.
    // mUF -- The map.

    Ugens := Setseq(Generators(UF));
    TotallyPositiveUnits := [];
    for v in CartesianPower([0,1], #Ugens) do
        unitelt := mUF(&*[Ugens[i] * v[i] : i in [1..#Ugens]]);
        if IsTotallyPositive(unitelt) then
            Append(~TotallyPositiveUnits, unitelt);
        end if;
    end for;
    return TotallyPositiveUnits;
end intrinsic;

// Artin Symbol
intrinsic ArtinSymbol(ZK::RngOrd, pp::RngOrdIdl) -> RngIntElt
{.}
    vprintf HilbertModularForms,1: "%o,%o,%o", ZK, pp, BaseRing(ZK);
    if not IsPrime(pp) then
	fac := Factorization(pp);
	return &*([1] cat [ArtinSymbol(fac, p[1]) : p in fac | IsOdd(p[2])]);
    end if;
    if IsSplit(pp,ZK) then return 1;
    elif IsRamified(pp,ZK) then return 0;
    else return -1; end if;
end intrinsic;


////////////////////////////////////////////////////////////////////////////////
//
// Local optimal embedding numbers.
//
////////////////////////////////////////////////////////////////////////////////

function OddLocalEmbeddingNumber(d, e, f, pp)
    // Returns the number of embeddings of the order of conductor pp^f in
    // a local quadratic order of discriminant d into an Eichler order of level pp^e.

    k, mk := ResidueClassField(pp);
    kappa := #k;
    pi := SafeUniformiser(pp);
    r := Valuation(d,pp);
    if IsSquare(mk(d/pi^r)) then
        issq := 2;
    else
        issq := 0;
    end if;

    if r eq 0 then
        return issq;
    elif e lt r then
        if e mod 2 eq 1 then
            return 2*kappa^((e-1) div 2);
        else
            return kappa^((e div 2)-1)*(kappa+1);
        end if;
    elif e eq r then
        if r mod 2 eq 1 then
            return kappa^((r-1) div 2);
        else
            return kappa^(r div 2) + kappa^((r div 2)-1)*issq;
        end if;
    elif e gt r then
        if r mod 2 eq 1 then
            return 0;
        else
            return kappa^((r div 2)-1)*(kappa+1)*issq;
        end if;
    end if;
end function;

function EvenQuadraticHenselLift(t, n, pp, m : Al := "Brutal")
  // Returns all solutions to x^2 - t*x + n = 0 (mod pp^m)

  Z_F := Order(pp);
  e := Valuation(Z_F!2,pp);

  pi := SafeUniformiser(pp);
  k, mk := ResidueClassField(pp);

  if Al eq "Brutal" then
    // Brutal enumeration
    sols := [];
    for u in CartesianPower(k,m) do
      x := &+[u[i]@@mk*pi^(i-1) : i in [1..m]];
      if Valuation(x^2-t*x+n,pp) ge m then
        Append(~sols, x);
      end if;
    end for;
    return sols;
  end if;

  // Otherwise, use a Hensel lift, probably could use some debugging.
  // For low-enough levels the algorithm is not really any faster.

  PiEltSeq := function(u,m);
    useq := [];
    for i := 1 to m do
      useq cat:= Eltseq(mk(u));
      u := (u-mk(u)@@mk)/pi;
    end for;
    return useq;
  end function;
  if m lt e then
    mm := m;
  else
    mm := e;
  end if;
  M := Matrix([ PiEltSeq(x^2-t*x,mm) : x in [u@@mk*pi^i : u in Basis(k), i in [0..mm-1]] ] cat
                [PiEltSeq(-n,mm)] );
  d := #Basis(k);
  N := [v : v in Nullspace(M) | v[mm*d+1] ne 0];
  N := [[ v[i]/v[mm*d+1] : i in [1..mm*d] ] : v in N];
  Nscal := [ u@@mk*pi^i : u in Basis(k), i in [0..mm-1] ];
  N := [&+[ v[i]@@mk*Nscal[i] : i in [1..mm*d]] : v in N];
  if m le e then
    return N;
  end if;

  if m lt 2*e then
    mm := m;
  else
    mm := 2*e;
  end if;
  N4 := [];
  for x in N do
    if t eq 0 then
      if Valuation(x^2-t*x+n,pp) ge mm then
        Append(~N4, x);
      end if;
    else
      fx := x^2-t*x+n;
      vt := Valuation(t,pp);
      if Valuation(fx/2,pp) ge Min(mm-e,vt) then
        if Valuation(fx/2,pp) ge mm-e then
          for u in CartesianPower(k,mm-e) do
            Append(~N4, x+2*&+[u[i]@@mk*pi^(i-1) : i in [1..mm-e]]);
          end for;
        else
          z := fx/pi^vt*(mk(pi^vt/t)@@mk);
          for u in CartesianPower(k,vt) do
            Append(~N4, x+z+pi^(mm-vt)*&+[u[i]@@mk*pi^(i-1) : i in [1..vt]]);
          end for;
        end if;
      end if;
    end if;
  end for;
  if m le 2*e then
    return N4;
  end if;

  for x in N4 do
    if Valuation(x^2-t*x+n,pp) lt 2*e then
      error "Failed solution", x;
    end if;
  end for;

  return N4;
end function;

function EvenLocalEmbeddingNumber(t, n, e, pp)
    if Valuation(t^2-4*n,pp) eq 0 then
        emb := #[x : x in EvenQuadraticHenselLift(t,n,pp,e) | Valuation(2*x-t,pp) ge 0];
    else
        q, mq := quo<Order(pp) | pp^(e)>;
        emb := #[x : x in EvenQuadraticHenselLift(t,n,pp,e) | Valuation(2*x-t,pp) ge 0] +
               #{mq(x) : x in EvenQuadraticHenselLift(t,n,pp,e+1) | Valuation(2*x-t,pp) ge 0};
    end if;
    return emb;
end function;

// Main thing we call.
function ActualLocalOptimalEmbeddingNumbers(F, level, OrderS, dff)
    // This function is based off of the function EllipticInvariants
    // within "Magma/package/Geometry/GrpPSL2/GrpPSL2Shim/shimura.m".
    //
    // NOTE: In our case, the discriminant of the quaternion algebra is 1, because
    // for a HMS the relevant quaternion algebra is M2(ZF).
    
    ZK := MaximalOrder(OrderS);
    ZF := MaximalOrder(F);    
    
    // Embedding numbers for primes dividing N are complicated!
    embeddingCount := 1;
    for qq in Factorization(level) do
        dffzk := dff * PseudoBasis(Module(ZK))[2][1];
        e := Valuation(dffzk, qq[1]);
        if dffzk eq qq[1]^e then
            dffzkpF := [];
        else
            dffzkpF := Factorization(dffzk/qq[1]^e);
        end if;
        u := WeakApproximation([pp[1] : pp in dffzkpF] cat [qq[1]],
                               [pp[2] : pp in dffzkpF] cat [0]);
        pi := SafeUniformiser(qq[1]);
        alpha := u * ZK.2 * pi^e;
        f := Eltseq(MinimalPolynomial(alpha));

        if Norm(qq[1]) mod 2 eq 0 then
            embeddingCount *:= EvenLocalEmbeddingNumber(-f[2],f[1], qq[2], qq[1]);
        else
            embeddingCount *:= OddLocalEmbeddingNumber(f[2]^2-4*f[1], qq[2],
                                                       Valuation(dff, qq[1]), qq[1]);
        end if;
    end for;
    return embeddingCount;
end function;

////////////////////////////////////////////////////////////////////////////////
//
// Old optimal embedding numbers.
//
////////////////////////////////////////////////////////////////////////////////

function LocalOptimalEmbeddingNumbers(b1, a1, prime, exponent)
    // Compute the number of local embeddings of the monogenic order
    // x^2 + b1 * x + a1.
    return EmbeddingNumbers(b1, a1, prime, exponent);
end function;


function OrderWithConductor(ZK, ff)
    // Given ff, return an order in ZK whose conductor is ff.
    K  := NumberField(ZK);
    noIdeaWhatThis := Generators(PseudoBasis(Module(ZK))[2][1]);

    Oq := sub<ZK | [K ! g * zki * ZK.2 : g in Generators(ff), zki in noIdeaWhatThis]>;
    return Oq;
end function;


function NumberOfAdelicOptimalEmbeddings(ZF, level, pair)
    // Preliminaries
    b := pair[1];
    a := pair[2];
    D := b^2-4*a;
    F := NumberField(ZF);
    // _<x> := PolynomialRing(F);
    // K := ext<F | x^2 - D >; 
    // ZK := Integers(K); 
    // DD := Discriminant(ZK); 

    //ff := Sqrt((D*ZF)/DD); // Conductor   
    //Kabs := AbsoluteField(K);
    //ZKabs := Integers(Kabs);
    //UK,mUK := UnitGroup(ZKabs);
    //_, mKabstoK := IsIsomorphic(Kabs,K);
    
    term := 1;
    for pp in Factorization(level) do  
        term *:= LocalOptimalEmbeddingNumbers(pair[1], pair[2], pp[1], pp[2]);
    end for;
    return term;
end function;

intrinsic OrdersContaining(ZK, S) -> Any
{Given an order S contained in the maximal order ZK for a number field K, 
compute all orders in K containing S.
It is assumed that S is generated by ZK.1 .}

    ZF := BaseRing(ZK);
    K  := NumberField(ZK);
    assert ZK.1 eq ZK ! S.1; // Sanity check.
    
    Dq := Discriminant(MinimalPolynomial(K.1));
    ff := SquareRoot(ZF !! Discriminant(S)/Discriminant(ZK));
    
    UK, mUK := UnitGroup(AbsoluteOrder(ZK));
    wK := #TorsionSubgroup(UK);

    // Loop over orders by their conductor dff.
    orders := [];
    conductors := [];
    for dff in Divisors(ff) do
        Append(~orders, OrderWithConductor(ZK, dff));
        Append(~conductors, dff);
    end for;

    return orders, conductors;
end intrinsic;


intrinsic OrderTermData(F::FldNum, Group::MonStgElt, rho::RngIntElt : Bound:=0) -> Rec
{Given a real quadratic field F, and some other parameter `rho`, returns the orders associated
to rho along with cached data needed to evaluate important quantities. The data is returned
as a record.}    
    // We want the automorphism of order 2q.
    assert IsEven(rho) and rho ne 2;

    if Group eq "GL+" and rho eq 4 then   // Special case of the formula.
        UF, mUF := UnitGroup(MaximalOrder(F));
        tpunits := TotallyPositiveUnitsModSquaresRepresentatives(UF, mUF);

        _<T> := PolynomialRing(F);        
        fieldList := [ext<F | T^2 + u> : u in tpunits];
    else
        fs := Factorization(CyclotomicPolynomial(rho), F)[1][1];
        fieldList := [ext<F | fs>];
    end if;
        
    return &cat[OrderTermDataForK(K : Bound:=Bound) : K in fieldList];
end intrinsic;

    
intrinsic OrderTermDataForK(K::FldNum : Bound := 0) -> Rec
{Given a quadratic extension K of a totally real field F, where K.1 corresponds to the
relevant generator of the order, compute all orders containing (ZF + K.1 * ZF).}

    F  := BaseField(K);
    ZK := MaximalOrder(K);
    ZF := MaximalOrder(F);
    Kabs := AbsoluteField(K);

    // This is the hugely expensive step.
    if Bound cmpeq 0 then
        hK := ClassNumber(Kabs);
    elif Bound cmpeq "BachBound" then
        hK := ClassNumber(Kabs : Bound := Floor(BachBound(Kabs)/40));
    else
        hK := ClassNumber(Kabs : Bound := Bound);
    end if;

    // Compute the order Oq = ZF[zeta_2s] and its conductor.
    S := Order([K.1]);

    // Cache unit groups.
    UK, mUK := UnitGroup(AbsoluteOrder(ZK));
    UF, mUF := UnitGroup(ZF);

    // Cache the discriminant and conductor.
    Dq := Discriminant(MinimalPolynomial(K.1));
    ff := SquareRoot(ZF !! Discriminant(S)/Discriminant(ZK));

    orders, conductors := OrdersContaining(ZK, S);
    Rdata := [];
    for i in [1..#orders] do
        Oq := orders[i]; dff := conductors[i];
        
        // We need the units.
        UOq, mUOq := UnitGroup(AbsoluteOrder(Oq));

        // We only take orders where Oq has exact torsion unit group of order s.
        // assert #TorsionSubgroup(UOq) eq s;

        // Picard number of the absolute order.
        OqUnitsInK := [mUOq(u) @@ mUK : u in Generators(UOq)];        
        
        // Factors de Artin.
        Fartin := [1 - UnramifiedSquareSymbol(Dq, pp[1])/AbsoluteNorm(pp[1])
                   : pp in Factorization(dff)];

        hOq := hK / #quo<UK | OqUnitsInK> * AbsoluteNorm(dff) * Product(Fartin);
        assert hOq eq #PicardGroup(AbsoluteOrder(Oq));

        // The local unit adjustment. (Hasse unit index)
        UQ  :=  sub<UF | [Norm(ZK ! mUOq(u)) @@ mUF : u in Generators(UOq)]>;
        QOq := #quo<UQ | [2*u : u in Generators(UF)]>;

        Append(~Rdata, rec<OrderTermRecordFormat | Order:=Oq,   
                                                   Conductor:=dff,  
                                                   PicardNumber:=hOq,
                                                   HasseUnitIndex:=QOq>);
    end for;
    
    return Rdata;
end intrinsic;


function PossibleIsotropyOrders(F)
    // Possible stabilizers for elliptic points. (Including -I.)

    S := LCM(CyclotomicQuadraticExtensions(F));
    // S = all prime powers m such that [F(zeta_m):F] = 2
    // Now get all possible m such that [F(zeta_m):F] = 2
    Sdiv := [m : m in Divisors(S) | m ne 1 and Valuation(m,2) ne 1]; // avoid repetition
    Sdiv := [m : m in Sdiv | 
             forall{ f : f in Factorization(CyclotomicPolynomial(m), F)
                     | Degree(f[1]) eq 2} ];
    Sdiv := [IsEven(m) select m else 2*m : m in Sdiv];

    return Sdiv;    
end function;

////////////////////////////////////////////////////////////////////////////////
//
// Main functionality.
//
////////////////////////////////////////////////////////////////////////////////

intrinsic CountEllipticPoints(Gamma::StupidCongruenceSubgroup : Group:="SL") -> Any
{Given a congruence subgroup `Gamma` (level, field, decoration data), return
}
    // The algorithm is based on page 739 of "Quaternion Algebra, Voight".
    // Essentially, we count optimal embeddings of the order generated by the
    // isotropy group of the elliptic point into Gamma, up to conjugation.
    //
    // In the notation of JV, the number of embeddings of S into O, up to conjugation
    // by Gamma is m(S, O; Gamma).

    F  := Field(Gamma);
    ZF := MaximalOrder(F);
    hF := ClassNumber(ZF);
    hFplus := NarrowClassNumber(F);

    dim := Degree(F); // Dimension of Hilbert modular variety.
    assert dim eq 2;
    level := Level(Gamma);


    ellipticCounts := AssociativeArray();
    ellipticCountsByOrder := AssociativeArray();

    isoOrds := PossibleIsotropyOrders(F);
    for rho in isoOrds do
        listOfOrders := OrderTermData(F, Group, rho);
        count := 0;

        for Srec in listOfOrders do
            // Extract Record data
            S   := Srec`Order;
            dff := Srec`Conductor;
            hS  := Srec`PicardNumber;
            QS  := Srec`HasseUnitIndex;
            
            // localCount := 1; // TODO: Generalize to other levels.
            // localCount := NumberOfAdelicOptimalEmbeddings(ZF, level, Stuple);
	    localCount := ActualLocalOptimalEmbeddingNumbers(F, level, S, dff);

            if Group eq "SL" then
                // The case of van der Geer -- PSL_2 acting on upper-half-plane-squared HH^2.
                // The forumla in Proposition 4.2.3 says that the number of elliptic points
                // is
                //
                //     mq^1 = 2^(n-1)/h(R) * Sum(S; h(S)/Q(S) * m(hatS, hatO; hatOtimes)).
                //
                // Where Q(S) is the Hasse Unit Index. We loop over the terms S.

                // NOTE: Factor of 2 in the paper, not in John's book.
                groupCorrectionFactor := 2^(dim-1) / (hF * QS);
                
            elif Group eq "GL+"  then
                // The forumla in Proposition 4.2.3 says that the number of elliptic points
                // is
                //
                //     mq^1 = 2^(n-1)/h^+(R) * Sum(S; h(S) * m(hatS, hatO; hatOtimes)).
                //
                groupCorrectionFactor := 2^(dim-1) / hFplus;

            else
                error "Case for group not implemented. Group := ", Group;
            end if;

            // Record the data into the table.
            ellipticCountsByOrder[S] := hS * groupCorrectionFactor * localCount;
            count +:= hS * groupCorrectionFactor * localCount;
        end for;

        ellipticCounts[ExactQuotient(rho, 2)] := count;        
    end for;

    return ellipticCounts, ellipticCountsByOrder;    
end intrinsic;


////////////////////////////////////////////////////////////////////////////////
//
// Testing.
//
////////////////////////////////////////////////////////////////////////////////

intrinsic _FieldAndGroup(n) -> Any
{}
    F := QuadraticField(n);
    G := CongruenceSubgroup(F);
    return F, G;
end intrinsic;

intrinsic TestEC(n)
{}
    F, G := _FieldAndGroup(n);
    A, B := CountEllipticPoints(G);
    print "Results:";
    print Eltseq(A);
    // print Eltseq(B);
end intrinsic;

intrinsic TestECGL(n)
{}
    F, G := _FieldAndGroup(n);
    A, B := CountEllipticPoints(G : Group:="GL+");
    print "Results:";
    print Eltseq(A);
    // print Eltseq(B);
end intrinsic;

intrinsic ActualCorrectOrders(F::FldNum, rho : Bound := 0) -> Tup
{For a totally real field F, computes and stores the class numbers 
 and associated data for all cyclotomic quadratic extensions of F.}

  ZF := MaximalOrder(F);
  UF, mUF := UnitGroup(ZF);

  // Order of the torsion element.
  s := rho;

  // TODO: Should be able to choose K as sqrt(-u) for some totally positive unit u.
  
  // vprintf Shimura : "Computing class number for %o\n", s;
  fs := Factorization(CyclotomicPolynomial(s), F)[1][1];
  K  := ext<F | fs>;
  ZK := MaximalOrder(K);
  Kabs := AbsoluteField(K);

  // This is the hugely expensive step.
  if Bound cmpeq 0 then
      hK := ClassNumber(Kabs);
  elif Bound cmpeq "BachBound" then
      hK := ClassNumber(Kabs : Bound := Floor(BachBound(Kabs)/40));
  else
      hK := ClassNumber(Kabs : Bound := Bound);
  end if;

  // Compute the order Oq = ZF[zeta_2s] and its conductor.
  Oq := Order([K.1]);
  Dq := Discriminant(MinimalPolynomial(K.1));
  ff := SquareRoot(ZF!!Discriminant(Oq)/Discriminant(ZK));

  UK, mUK := UnitGroup(AbsoluteOrder(ZK));
  wK := #TorsionSubgroup(UK);

  Rdata := [];

  // Loop over orders by their conductor dff.
  for dff in Divisors(ff) do
      
      // if ZK is maximal, we have Cl(O_dff)/Cl(K) = 1.
      if dff eq ideal<ZF | 1> then
          Oq := ZK;
          UOq := UK;
          mUOq := mUK;
          wOq := wK;
          hOq := hK; 

      else
          // Otherwise, use the classic formula to compute the relative class number.
          Oq := OrderWithConductor(ZK, dff);          
          UOq, mUOq := UnitGroup(AbsoluteOrder(Oq));

          // We only take orders where Oq has exact torsion unit group of order s.
          assert #TorsionSubgroup(UOq) eq s;

          // Picard number of the absolute order.
          OqUnitsInK := [mUOq(u) @@ mUK : u in Generators(UOq)];
          
          hOq := hK/#quo<UK | OqUnitsInK> * AbsoluteNorm(dff) *
                    &*[1-UnramifiedSquareSymbol(Dq, pp[1])/AbsoluteNorm(pp[1])
                       : pp in Factorization(dff)];
          
          assert hOq eq #PicardGroup(AbsoluteOrder(Oq));
          // hOq := #PicardGroup(AbsoluteOrder(Oq));
      end if;

      
      // The local unit adjustment. (Hasse unit index)
      UQ  := sub<UF | [Norm(ZK ! mUOq(u)) @@ mUF : u in Generators(UOq)]>;
      QOq := #quo<UQ | [2*u : u in Generators(UF)]>;
      // QOq := HasseUnitIndex(Oq);
      //hQOq := hOq/QOq;


      // dff  -- divisor of conductor of R[i].
      // hOq  -- Class number of the order S.
      // QOq  -- Hasse Unit index of the order S.
      Append(~Rdata, <dff, hOq, Rationals() ! QOq>);
  end for;

  return Rdata;
end intrinsic;

