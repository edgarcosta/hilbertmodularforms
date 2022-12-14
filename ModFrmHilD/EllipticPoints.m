
// Artin Symbol
function ArtinSymbol(ZK, pp)
    if IsSplit(pp,ZK) then return 1;
    elif IsRamified(pp,ZK) then return 0;
    else return -1; end if;
end function;

function HasseUnitIndex(ZF, pair)
    // Compute the Hasse unit index of the order associated to the monogenic order.

    // First create the monogenic order
    F := NumberField(ZF);
    _<x> := PolynomialRing(ZF);
    K := ext<NumberField(ZF) | x^2 + pair[1] * x + pair[2]>;
    ZK := MaximalOrder(K);
    S := Order([K.1]);

    // Get the image of the norm from units of S in F^x.
    US, mUS := UnitGroup(AbsoluteOrder(S));
    UF, mUF := UnitGroup(ZF);

    UQ := sub<UF | [Norm(ZK ! mUS(u)) @@ mUF : u in Generators(US)]>;
    
    // Now we need to compute ZF^(x2). Observe that
    //
    //  2^(r1+r2 - 1) * |<-1>| = [ZF^x : ZF^(x2)] = [ZF^x : UQ] [UQ : ZF^(x2)];
    //
    // because F is totally real and due to the Dirichlet unit theorem.    
    return ExactQuotient(2^Degree(F), Index(UF, UQ));
end function;

function LocalOptimalEmbeddingNumbers(b1, a1, prime, exponent)
    // Compute the number of local embeddings of the monogenic order
    // x^2 + b1 * x + a1.
    return EmbeddingNumbers(b1, a1, prime, exponent);
end function;

function ClassNumberOfOrderWithConductor(ZK, bb)
    // Class number of the order with conductor bb.
    factsbb := Factorization(bb);
    // NOTE: Replace ArtinSymbol with UnramifiedSquareSymbol
    artinFactors := [1 - ArtinSymbol(ZK, pp[1]) * Norm(pp[1])^(-1) : pp in factsbb];
    term := IsEmpty(factsbb) select Norm(bb) else Norm(bb) * (&* artinFactors);

    // print ClassNumber(AbsoluteOrder(ZK));
    return ClassNumber(AbsoluteOrder(ZK)) * term;
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


intrinsic ActualCorrectOrders(F::FldNum, rho : Bound := 0) -> Tup
{For a totally real field F, computes and stores the class numbers 
 and associated data for all cyclotomic quadratic extensions of F.}

  ZF := MaximalOrder(F);
  UF, mUF := UnitGroup(ZF);

  hKs := [];
  Rs := [];
  ZKs := [];

  // Order of the torsion element.
  s := rho;
  
  // vprintf Shimura : "Computing class number for %o\n", s;
  fs := Factorization(CyclotomicPolynomial(s), F)[1][1];
  K := ext<F | fs>;
  ZK := MaximalOrder(K);
  // ZKs[i] := ZK;

  Kabs := AbsoluteField(K);

  // This is the hugely expensive step.
  if Bound cmpeq 0 then
      hK := ClassNumber(Kabs);
  elif Bound cmpeq "BachBound" then
      hK := ClassNumber(Kabs : Bound := Floor(BachBound(Kabs)/40));
  else
      hK := ClassNumber(Kabs : Bound := Bound);
  end if;
  // hKs[i] := hK;

  // Compute the order Oq = ZF[zeta_2s] and its conductor.
  Oq := Order([K.1]);
  Dq := Discriminant(MinimalPolynomial(K.1));
  ff := SquareRoot(ZF!!Discriminant(Oq)/Discriminant(ZK));

  UK, mUK := UnitGroup(AbsoluteOrder(ZK));
  wK := #TorsionSubgroup(UK);

  Rdata := [];

  // Loop over orders by their conductor dff.
  for jf := 1 to #Divisors(ff) do
      dff := Divisors(ff)[jf];

      // if ZK is maximal, we have Cl(O_dff)/Cl(K) = 1.
      if dff eq ideal<ZF | 1> then
          Oq := ZK;
          UOq := UK;
          mUOq := mUK;
          wOq := wK;
          hOq := hK; // Different than John's function.
          // Otherwise, use the classic formula to compute the relative class number.
      else
          Oq := sub<ZK | [K!g*zki*ZK.2 : g in Generators(dff),
                                         zki in Generators(PseudoBasis(Module(ZK))[2][1])]>;
          UOq, mUOq := UnitGroup(AbsoluteOrder(Oq));
          wOq := #TorsionSubgroup(UOq);
          /* hOq := 1/#quo<UK | [mUOq(u)@@mUK : u in Generators(UOq)]> * AbsoluteNorm(dff) * */
          /*          &*[1-UnramifiedSquareSymbol(Dq,pp[1])/ */
          /*               AbsoluteNorm(pp[1]) : pp in Factorization(dff)]; */

          // print hOq, #PicardGroup(AbsoluteOrder(Oq));
          // assert hOq eq #PicardGroup(AbsoluteOrder(Oq));
          hOq := #PicardGroup(AbsoluteOrder(Oq));
      end if;

      // We only take orders where Oq has exact torsion unit group of order s.
      if wOq ne s*2/Gcd(2,s) then
          hQOq := 0;
      else
          // The local unit adjustment. (Hasse unit index)
          UQ := sub<UF | [Norm(ZK ! mUOq(u)) @@ mUF : u in Generators(UOq)]>;
          QOq := #quo<UQ | [2*u : u in Generators(UF)]>;
          //hQOq := hOq/QOq;
      end if;

      // dff  -- divisor of conductor of R[i].
      // hOq -- ????  Class number of the order S.
      // QOq  -- ????  Hasse Unit index of the order S.

      Append(~Rdata, <dff, hOq, Rationals() ! QOq>);
  end for;

  return Rdata;
end intrinsic;


intrinsic CountEllipticPoints(Gamma::StupidCongruenceSubgroup : Group:="SL") -> Any
{Given a congruence subgroup `Gamma` (level, field, decoration data), return
}
    // The algorithm is based on page 739 of "Quaternion Algebra, Voight".
    // Essentially, we count optimal embeddings of the order generated by the
    // isotropy group of the elliptic point into Gamma, up to conjugation.
    //
    // In the notation of JV, the number of embeddings of S into O, up to conjugation
    // by Gamma is m(S, O; Gamma).

    // First find all the S's.

    F := Field(Gamma);
    ZF := MaximalOrder(F);
    hF := ClassNumber(ZF);
    hFplus := NarrowClassNumber(F);
    dim := Degree(F); // Dimension of Hilbert modular variety.
    assert dim eq 2;

    // TODO: Level data might be important in order selection.
    level := Level(Gamma);
    assert Norm(level) eq 1;
    
    // The forumla in Proposition 4.2.3 says that the number of elliptic points
    // is
    //
    //     mq^+ = 2^(n-1)/h^+(R) * Sum(S; h(S) * m(hatS, hatO; hatOtimes).
    //
    // We loop over the terms S (valid monogenic orders that could be isotropy orders).

    ellipticCounts := AssociativeArray();
    ellipticCountsByOrder := AssociativeArray();

    // Loop over these values for some reason.
    S := LCM(CyclotomicQuadraticExtensions(F));
    // S = all prime powers m such that [F(zeta_m):F] = 2
    // Now get all possible m such that [F(zeta_m):F] = 2
    Sdiv := [m : m in Divisors(S) | m ne 1 and Valuation(m,2) ne 1]; // avoid repetition
    Sdiv := [m : m in Sdiv | 
             forall{ f : f in Factorization(CyclotomicPolynomial(m), F)
                     | Degree(f[1]) eq 2} ];
    Sdiv := [IsEven(m) select m else 2*m : m in Sdiv];

    for rho in Sdiv do
        listOfOrders := ActualCorrectOrders(F, rho);
        count := 0;
        
        for Stuple in listOfOrders do
            //hS := PicardNumberOfMonogenicOrder(ZF, Stuple);
            hS := Stuple[2];
            localCount := 1; // TODO: Generalize to other levels.
            // localCount := NumberOfAdelicOptimalEmbeddings(ZF, level, Stuple);

            
            // This particular term depends on the particular group of interest.
            if Group eq "SL" then
                // The case of van der Geer -- PSL_2 acting on upper-half-plane-squared HH^2.
                // The forumla in Proposition 4.2.3 says that the number of elliptic points
                // is
                //
                //     mq^1 = 2^(n-1)/h(R) * Sum(S; h(S)/Q(S) * m(hatS, hatO; hatOtimes)).
                //
                // Where Q(S) is the Hasse Unit Index. We loop over the terms S.

                //hasseUnitIndex := HasseUnitIndex(ZF, Stuple);
                hasseUnitIndex := Stuple[3];
                // print "Hasse:", hasseUnitIndex, rho;
                
                // NOTE: Factor of 2 in the paper, not in John's book.
                groupCorrectionFactor := 2^(dim-1) / hF / hasseUnitIndex;
                
                // print "Stuple:", Stuple[1], hS, localCount, hF, hasseUnitIndex;
                // print "Factor:", groupCorrectionFactor;
                
            elif Group eq "GL"  then
                groupCorrectionFactor := 2^(dim-1) / hFplus;

            else
                error "Case for group not implemented. Group := ", Group;
            end if;

            // Record the data into the table.
            ellipticCountsByOrder[Stuple[1]] := hS * groupCorrectionFactor * localCount;
            count +:= hS * groupCorrectionFactor * localCount;
        end for;

        ellipticCounts[ExactQuotient(rho, 2)] := count;
        
    end for;

    return ellipticCounts, ellipticCountsByOrder;    
end intrinsic;

intrinsic Foo(n) -> Any
{}
    F := QuadraticField(n);
    G := CongruenceSubgroup(F);
    return F, G;
end intrinsic;

intrinsic TestEC(n)
{}
    F, G := Foo(n);
    A, B := CountEllipticPoints(G);
    print "Results:";
    print Eltseq(A);
    // print Eltseq(B);
end intrinsic;
