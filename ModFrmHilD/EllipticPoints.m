////////////////////////////////////////////////////////////////////////////////
//
//     EllipticPoints.m
//
// Functionality for computing the number and types of elliptic points.
//
////////////////////////////////////////////////////////////////////////////////

// Types, Records, and Constants.
OrderTermRecordFormat := recformat<Order, Conductor, PicardNumber, HasseUnitIndex,
                                  NumberField, MaximalOrder, RotationElement>;

declare verbose EllipticPointsDebug, 1;
import "CongruenceSubgroup.m": GAMMA_0_Type;

////////////////////////////////////////////////////////////////////////////////
//
// Rotation label type
//
////////////////////////////////////////////////////////////////////////////////

declare type GrpHilbRotationLabel;
declare type GrpHilbRotationLabelUniversalParent[GrpHilbRotationLabel];
LABEL_UNIVERSAL_PARENT := New(GrpHilbRotationLabelUniversalParent);

// A rotation label consists of a triple <rho; a1, ..., an>, where rho is the order
// of the action of a finite order element on a product of Degree(F) upper
// half planes, and the local action of an element is given by
//
//     (z1, ..., zn) -> (zeta_rho^a1 * z1, ..., zeta_rho^an * zn)
//
// The rotation label is a property of a cyclic group, so two labels are equivalent
// if they are obtained by picking two different cyclic generators of the same group.
// That is, by picking a different rho-th root of unity.
//
// By definition, each ai is coprime to rho.
//
// Our interface allows the user to input any of the equivalent labels as a tuple
// and "Just work" for extracting elements from associative arrays, with the type
// doing equivalence checks in the background.

declare attributes GrpHilbRotationLabel : tuple;

intrinsic StandardizeRotationTuple(tup) -> Tup
{Standardize so that the label is of the form <n; 1, a2, ...>.}  
    n := tup[1];
    R := Integers(n);

    a1 := R ! tup[2];
    _, a1inv := IsInvertible(a1);

    return <n> cat <a1inv * tup[i] : i in [2..#tup]>;    
end intrinsic;

// Creation (Internal, the user shouldn't really notice
intrinsic HMVRotationLabel(tup::Tup) -> GrpHilbRotationLabel
{}
    msg := "Rotation order must be an integer larger than 1.";
    require ISA(Type(tup[1]), RngIntElt) and tup[1] gt 1: msg;

    require #tup gt 1: "Rotation tuple must be of the form <n, a1, ...>.";

    R := Integers(tup[1]);
    require &and [IsInvertible(R ! tup[i]) : i in [2..#tup]]: "Invalid rotation tuple.";
    
    L := New(GrpHilbRotationLabel);
    L`tuple := StandardizeRotationTuple(tup);
    return L;
end intrinsic;

intrinsic Tuple(L::GrpHilbRotationLabel) -> Tup
{Return the tuple attribute of the rotation label.}
    return L`tuple;
end intrinsic;

intrinsic IntegerTuple(L::GrpHilbRotationLabel) -> Tup
{Return the tuple attribute of the rotation label, with entries as integers.}
    return <Integers() ! x : x in Tuple(L)>;
end intrinsic;


// Print
intrinsic Print(L::GrpHilbRotationLabel)
{Print.}
    printf "Label%o", Tuple(L);
end intrinsic;

intrinsic Print(L::GrpHilbRotationLabelUniversalParent)
{Print.}
    printf "Universal parent for Hilbert Modular Rotation Labels.";
end intrinsic;


// eq
intrinsic 'eq'(L1::GrpHilbRotationLabelUniversalParent,
               L2::GrpHilbRotationLabelUniversalParent) -> BoolElt
{}
    return true;
end intrinsic;


intrinsic 'eq'(L1::GrpHilbRotationLabel, L2::GrpHilbRotationLabel) -> BoolElt
{}
    // Convert to standard form.
    tup1 := Tuple(L1);
    tup2 := Tuple(L2);

    if #tup1 ne #tup2 then return false; end if;
    if #tup1 ne #tup2 then return false; end if;
    
    
    // Compare.
    return Tuple(L1) eq Tuple(L2); // TODO: Update this to be correct.
end intrinsic;

intrinsic 'eq'(L1::GrpHilbRotationLabel, L2::Tup) -> BoolElt
{}
    return L1 eq HMVRotationLabel(L2);
end intrinsic;

intrinsic 'eq'(L1::Tup, L2::GrpHilbRotationLabel) -> BoolElt
{}
    return 'eq'(L2, L1);
end intrinsic;


// Parent (For hacky array key comparison purposes)
intrinsic Parent(L::GrpHilbRotationLabel) -> Any
{}
    return LABEL_UNIVERSAL_PARENT;
end intrinsic;

// Coercion
intrinsic IsCoercible(X::GrpHilbRotationLabelUniversalParent, y::Any) -> BoolElt, .
{Return whether y is coercible into X and the result if so}

    if Type(y) eq GrpHilbRotationLabel then
	return true, y;
    end if;

    if Type(y) eq Tup then
        return true, HMVRotationLabel(y);
    end if;
    
    return false, "Illegal coercion.";
end intrinsic;


////////////////////////////////////////////////////////////////////////////////
//
// Helper functions.
//
////////////////////////////////////////////////////////////////////////////////

intrinsic TotallyPositiveUnitsModSquaresRepresentatives(UF::GrpAb, mUF::Map) -> SeqEnum
{Compute representatives for the group of totally positive units modulo squares in
the associated number field. The first and second arguments should be the two outputs
of UnitGroup(F).}
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

intrinsic TotallyPositiveUnitsModSquaresRepresentatives(F::FldNum) -> SeqEnum
{.}
    ZF := MaximalOrder(F);
    UF, mUF := UnitGroup(F);
    return TotallyPositiveUnitsModSquaresRepresentatives(UF, mUF);
end intrinsic;

intrinsic IndexOfTotallyPositiveUnitsModSquares(F::FldNum) -> RngIntElt
{.}
    UF, mUF := UnitGroup(MaximalOrder(F));
    return #TotallyPositiveUnitsModSquaresRepresentatives(UF, mUF);
end intrinsic;

// Artin Symbol
intrinsic ArtinSymbol(ZK::RngOrd, pp::RngOrdIdl) -> RngIntElt
{.}
    vprintf HilbertModularForms,1: "%o,%o,%o", ZK, pp, BaseRing(ZK);
    if not IsPrime(pp) then
        fac := Factorization(pp);
        return &*([1] cat [ArtinSymbol(ZK, p[1]) : p in fac | IsOdd(p[2])]);
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


intrinsic CountAdelicOptimalEmbeddings(Gamma::GrpHilbert, Srec::Rec) -> RngIntElt
{Given a congruence subgroup `Gamma` and an order `S` (as a record), return the
number of embeddings of the adelic completion of `S` into the adelic completion of
`Gamma`.}
    // This function is based off of the function EllipticInvariants
    // within "Magma/package/Geometry/GrpPSL2/GrpPSL2Shim/shimura.m".
    //
    // NOTE: In our case, the discriminant of the quaternion algebra is 1, because
    // for a HMS the relevant quaternion algebra is M2(ZF).

    require GammaType(Gamma) eq GAMMA_0_Type : "Not implemented for non Gamma0 type";
    F      := BaseField(Gamma);
    level  := Level(Gamma);

    OrderS := Srec`Order;
    dff    := Srec`Conductor;
    
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
end intrinsic;

////////////////////////////////////////////////////////////////////////////////
//
// Orders
//
////////////////////////////////////////////////////////////////////////////////

/* function LocalOptimalEmbeddingNumbers(b1, a1, prime, exponent) */
/*     // Compute the number of local embeddings of the monogenic order */
/*     // x^2 + b1 * x + a1. */
/*     return OptimalEmbeddingNumber(b1, a1, prime, exponent); */
/* end function; */


function OrderWithConductor(ZK, ff)
    // Given ff, return an order in ZK whose conductor is ff.
    K  := NumberField(ZK);
    noIdeaWhatThis := Generators(PseudoBasis(Module(ZK))[2][1]);

    Oq := sub<ZK | [K ! g * zki * ZK.2 : g in Generators(ff), zki in noIdeaWhatThis]>;
    return Oq;
end function;


/* function NumberOfAdelicOptimalEmbeddings(ZF, level, pair) */
/*     // Preliminaries */
/*     b := pair[1]; */
/*     a := pair[2]; */
/*     D := b^2-4*a; */
/*     F := NumberField(ZF); */
/*     // _<x> := PolynomialRing(F); */
/*     // K := ext<F | x^2 - D >; */
/*     // ZK := Integers(K); */
/*     // DD := Discriminant(ZK); */

/*     //ff := Sqrt((D*ZF)/DD); // Conductor */
/*     //Kabs := AbsoluteField(K); */
/*     //ZKabs := Integers(Kabs); */
/*     //UK,mUK := UnitGroup(ZKabs); */
/*     //_, mKabstoK := IsIsomorphic(Kabs,K); */

/*     term := 1; */
/*     for pp in Factorization(level) do */
/*         term *:= LocalOptimalEmbeddingNumbers(pair[1], pair[2], pp[1], pp[2]); */
/*     end for; */
/*     return term; */
/* end function; */

intrinsic OrdersContaining(ZK, S) -> SeqEnum, SeqEnum
{Given an order S contained in the maximal order ZK for a number field K,
compute all orders in K containing S. It is assumed that S is generated by ZK.1 .}

    ZF := BaseRing(ZK);
    K  := NumberField(ZK);
    // assert K.1 eq K ! S.2; // Sanity check.

    // Dq := Discriminant(MinimalPolynomial(K.1));
    ff := SquareRoot(ZF !! Discriminant(S)/Discriminant(ZK));

    UK, mUK := UnitGroup(AbsoluteOrder(ZK));
    // wK := #TorsionSubgroup(UK);

    // Loop over orders by their conductor dff.
    orders := [];
    conductors := [];
    for dff in Divisors(ff) do
        Append(~orders, OrderWithConductor(ZK, dff));
        Append(~conductors, dff);
    end for;

    return orders, conductors;
end intrinsic;


intrinsic OrderTermData(G::GrpHilbert, F::FldNum, rho::RngIntElt : Bound:=0) -> SeqEnum[Rec]
{Given a real quadratic field F, and some other parameter `rho`, returns the orders associated
to rho along with cached data needed to evaluate important quantities. The data is returned
as a record.}
    // We want the automorphism of order 2q.
    assert IsEven(rho) and rho ne 2;

    if AmbientType(G) eq GLPlus_Type then  // Special case of the formula.
        UF, mUF := UnitGroup(MaximalOrder(F));
        tpunits := TotallyPositiveUnitsModSquaresRepresentatives(UF, mUF);

        _<T> := PolynomialRing(F);
        if rho eq 4 then
            fieldList := [ext<F | T^2 + u> : u in tpunits];
        elif rho eq 6 then
            fieldList := [ext<F | T^2 - T + 1>];
        elif rho eq 8 then
            fieldList := [];
            for u in tpunits do
                is_sqr, t := IsSquare(2*u);
                if is_sqr then
                    Append(~fieldList, ext<F | T^2 - t*T + u>);
                end if;
            end for;
        elif rho eq 12 then
            fieldList := [];
            for u in tpunits do
                is_sqr, t := IsSquare(3*u);
                if is_sqr then
                    Append(~fieldList, ext<F | T^2 - t*T + u>);
                end if;
            end for;
        elif rho eq 24 then
            is_sqr, sqrt3 := IsSquare(F!3);
            if not is_sqr then return []; end if;
            fieldList := [];
            for u in tpunits do
                is_sqr, t := IsSquare((2+sqrt3)*u);
                if is_sqr then
                    Append(~fieldList, ext<F | T^2 - t*T + u>);
                end if;
            end for;
        else
            fs := Factorization(CyclotomicPolynomial(rho), F)[1][1];
            if (Degree(fs) ne 2) then return []; end if;
            fieldList := [ext<F | fs>];
            // error "Not implemented for this order";
        end if;
    elif AmbientType(G) eq SL_Type then
        fs := Factorization(CyclotomicPolynomial(rho), F)[1][1];
        if (Degree(fs) ne 2) then return []; end if;
        fieldList := [ext<F | fs>];
    else
        error "Unknown Ambient type for Congruence Subgroup: ", AmbientType(G);
    end if;

    return &cat[OrderTermDataForK(K : Bound:=Bound) : K in fieldList];
end intrinsic;


intrinsic OrderTermDataForK(K::FldNum : Bound := 0) -> SeqEnum[Rec]
{Given a quadratic extension K of a totally real field F, where K.1 corresponds to the
relevant generator of the order, compute all orders containing (ZF + K.1 * ZF).}

    vprint EllipticPointsDebug: K, Type(K), Discriminant(K);

    F  := BaseField(K);
    ZK := MaximalOrder(K);
    ZF := MaximalOrder(F);
    Kabs := AbsoluteField(K);
    ZKabs := AbsoluteOrder(ZK);

    // This is the hugely expensive step.
    if Bound cmpeq 0 then
        hK := ClassNumber(Kabs);
    elif Bound cmpeq "BachBound" then
        hK := ClassNumber(Kabs : Bound := Floor(BachBound(Kabs)/40));
    else
        hK := ClassNumber(Kabs : Bound := Bound);
    end if;

    _ := IndependentUnits(ZKabs);
    SetOrderUnitsAreFundamental(ZKabs);
    UK, mUK := UnitGroup(ZKabs);
    // This is necessary so that the UnitGroup(s) below are done
    // with the same level of rigour as the ClassGroup above.
    // Without this, the UnitGroup would be done with full rigour,
    // But that is pointless: if hK was heuristic and incorrect,
    // then our answer will be wrong even if we get the units right.
    // (Oct 2010, SRD)


    // Compute the order Oq = ZF[g] and its conductor.
    S := Order([K.1]);
    zeta := K.1;
    t := Trace(zeta);
    u := Norm(zeta);

    // Cache unit groups.
    UK, mUK := UnitGroup(ZKabs);
    UF, mUF := UnitGroup(ZF);

    // F is totally real, so the quotient consists only of
    // quotient of the torsion subgroups

    FUnitIndexInK := #TorsionSubgroup(UK) div 2;

    // Cache the discriminant and conductor.
    D := Discriminant(ZF);
    Dq := Discriminant(MinimalPolynomial(K.1));
    ff := SquareRoot(ZF !! Discriminant(S)/Discriminant(ZK));

    orders, conductors := OrdersContaining(ZK, S);
    Rdata := [];

    // print ZK, UK, [mUK(g) : g in Generators(UK)];

    for i in [1..#orders] do
        Oq := orders[i]; dff := conductors[i];

        vprint EllipticPointsDebug : "Order:", AbsoluteOrder(Oq) : Magma;
        vprint EllipticPointsDebug : "Conductor:", dff;

        // We need the units.
        UOq, mUOq := UnitGroup(AbsoluteOrder(Oq));

        // We only take orders where Oq has exact torsion unit group of order s.
        // assert #TorsionSubgroup(UOq) eq s;

        // Picard number of the absolute order.
        OqUnitsInK := [(K ! Oq ! mUOq(u)) @@ mUK : u in Generators(UOq)];

        vprint EllipticPointsDebug : "Oqunits: ", [mUK(g) : g in OqUnitsInK];
        vprint EllipticPointsDebug : "Oqunits in K:", OqUnitsInK;

        // Factors de Artin.
        Fartin := [1 - UnramifiedSquareSymbol(Dq, pp[1])/AbsoluteNorm(pp[1])
                   : pp in Factorization(dff)];

        hOq := hK / #quo<UK | OqUnitsInK> * AbsoluteNorm(dff) * Product(Fartin);

        vprint EllipticPointsDebug : "Picard:", hOq;
        vprint EllipticPointsDebug : "John Picard:",
                                     JohnPicardNumberCode(ZKabs, ZK, UK, mUK, Dq, dff);

        vprint EllipticPointsDebug : "Receipt:", hK,  #quo<UK | OqUnitsInK>,
                                     AbsoluteNorm(dff) , Product(Fartin);

        assert hOq eq #PicardGroup(AbsoluteOrder(Oq));

        // The local unit adjustment. (Hasse unit index)
        UQ  :=  sub<UF | [Norm(ZK ! mUOq(u)) @@ mUF : u in Generators(UOq)]>;
        QOq := #quo<UQ | [2*u : u in Generators(UF)]>;

        Append(~Rdata, rec<OrderTermRecordFormat | Order:=Oq,
                                                   Conductor:=dff,
                                                   PicardNumber:=hOq,
                                                   HasseUnitIndex:=QOq,
                                                   NumberField:=K,
                                                   MaximalOrder:=ZK,
                                                   RotationElement:=zeta>);
    end for;

    return Rdata;
end intrinsic;


function PossibleIsotropyOrders(F)
    // Possible stabilizers for elliptic points. (Including -I.)

    S := LCM(CyclotomicQuadraticExtensions(F));
    // S = all prime powers m such that [F(zeta_m):F] = 2
    // Now get all possible m such that [F(zeta_m):F] = 2
    Sdiv := [m : m in Divisors(S) | m ne 1 and Valuation(m,2) ne 1]; // avoid repetition
    Sdiv_final := {2*m : m in Sdiv} join {m : m in Sdiv | IsEven(m)};

    return Sort([m : m in Sdiv_final]);
end function;

////////////////////////////////////////////////////////////////////////////////
//
// Rotation types.
//
////////////////////////////////////////////////////////////////////////////////

function RotationFactorPossibilities(ell_order)
    // Get the possible rotation types for the given order.
    
    U, mU := UnitGroup(Integers(ell_order));
    U2,i1,i2,pi1,pi2 := DirectSum(U,U);
    T := pi1(Kernel(hom<U2 -> U | [pi1(U2.x) + pi2(U2.x) : x in [1..Ngens(U2)]]>));
    rot_factors := [[q,1] : q in Reverse(Sort([mU(g) : g in T]))];

    return rot_factors;
end function;

intrinsic RotationFactors(zeta::FldNumElt, q::RngIntElt) -> SeqEnum[RngIntElt]
{Given an element `zeta` of finite order `q` in `K^\times/R^\times`, where `K` is a CM extension
of a totally real field `F` and `R` is the ring of integers of `F`, return the rotation factors
associated to the action of `zeta` on the Degree(F)-fold product of upper half planes.}

  F := BaseField(Parent(zeta));
  s := Trace(zeta);
  n := Norm(zeta);
  a := s^2/(2*n) - 1;
  CC<i> := ComplexField();
  alphas := RealEmbeddings(a);
  signs_s := [Sign(x) : x in RealEmbeddings(s)];
  
  alpha0 := [alphas[j] - i*signs_s[j] * Sqrt(1 - alphas[j]^2) :
             j in [1..Degree(F)]];

  // Here we assume it is a surface
  assert exists(t){t : t in [1..q-1] | Abs(alpha0[1]^t - alpha0[2]) lt Exp(-20)};

  rplus := HMVRotationLabel(<q, t, 1>);
  rminu := HMVRotationLabel(<q, q-t, 1>);
  return rplus, rminu;
end intrinsic;

/* intrinsic RotationFactors(zeta::FldNumElt, q::RngIntElt) -> SeqEnum[RngIntElt], SeqEnum[RngIntElt] */
/* {Given an element `zeta` of finite order in `K^\times/R^\times`, where `K` is a CM extension */
/* of a totally real field `F` and `R` is the ring of integers of `F`, return the rotation factors */
/* associated to the action of `zeta` on the Degree(F)-fold product of upper half planes.} */
/*     rot_factor := RotationFactor(zeta, q); */
/*     rot_factor_minus := [q - rot_factor[1], rot_factor[2]]; */
/*     return rot_factor, rot_factor_minus; */
/* end intrinsic;     */


////////////////////////////////////////////////////////////////////////////////
//
// Counting by order
//
////////////////////////////////////////////////////////////////////////////////

intrinsic AreEmbeddingsOrientedOptimallySelective(Srec::Rec, Gamma::GrpHilbert) -> BoolElt
{}
    K  := Srec`NumberField;
    ZK := Srec`MaximalOrder;
    level := Level(Gamma);
    require GammaType(Gamma) eq GAMMA_0_Type : "Gamma type not supported.";
    
    is_unr := IsUnramified(K);
    level_cond := &and[IsSplit(p_e[1], ZK) : p_e in Factorization(level) | IsOdd(p_e[2])];

    return is_unr and level_cond;
end intrinsic;

intrinsic CountEllipticPoints(Gamma::GrpHilbert, Srec::Rec, hF, hFplus) -> RngIntElt, RngIntElt
{Given a congruence subgroup `Gamma` and an order S (with additional data), counts
the number of elliptic points whose associated order admits an embedding of S. The two
integers returned are the rotation orders for the plus type and minus type, respectively.}

    // Extract Record data
    S   := Srec`Order;
    dff := Srec`Conductor;
    hS  := Srec`PicardNumber;
    QS  := Srec`HasseUnitIndex;
    K   := Srec`NumberField;
    ZK  := Srec`MaximalOrder;

    dim   := Degree(BaseField(Gamma));
    level := Level(Gamma);
    
    if AmbientType(Gamma) eq SL_Type then
        // The case of van der Geer -- PSL_2 acting on upper-half-plane-squared HH^2.
        // The forumla in Proposition 4.2.3 says that the number of elliptic points
        // is
        //
        //     mq^1 = 2^(n-1)/h(R) * Sum(S; h(S)/Q(S) * m(hatS, hatO; hatOtimes)).
        //
        // Where Q(S) is the Hasse Unit Index. We loop over the terms S.

        // NOTE: Factor of 2 in the paper, not in John's book.
        groupCorrectionFactor := 2^(dim-1) / (hF * QS);

    elif AmbientType(Gamma) eq GLPlus_Type then
        // The forumla in Proposition 4.2.3 says that the number of elliptic points
        // is
        //
        //     mq^1 = 2^(n-1)/h^+(R) * Sum(S; h(S) * m(hatS, hatO; hatOtimes)).
        //
        groupCorrectionFactor := 2^(dim-1) / hFplus;

    else
        error "Case not implemented for Ambient Type", AmbientType(Gamma);
    end if;

    // Adelic count
    localCount := CountAdelicOptimalEmbeddings(Gamma, Srec);
    
    // Record the data into the table.
    total_num := Integers() ! (hS * groupCorrectionFactor * localCount);

    vprint EllipticPointsDebug : S, Norm(Norm(Conductor(S)));
    vprint EllipticPointsDebug : localCount, total_num, groupCorrectionFactor, hS;

    
    // YYY: Check which signs occur (CM types) via oriented optimal selectivity.
    if AreEmbeddingsOrientedOptimallySelective(Srec, Gamma) then
        // assert OrderNormIndex(S) eq 2;

        a := SteinitzClass(Module(S));
        sign := ArtinSymbol(ZK, a*Component(Gamma));
        if (sign eq 1) then
            num_plus  := total_num;
            num_minus := 0;
        else
            num_plus  := 0;
            num_minus := total_num;
        end if;
    else
        assert IsEven(total_num);
        num_plus := total_num div 2;
        num_minus := total_num div 2;
    end if;

    return num_plus, num_minus;
end intrinsic;

////////////////////////////////////////////////////////////////////////////////
//
// Update functions
//
////////////////////////////////////////////////////////////////////////////////

procedure UpdateCountArray(~Counts, key, value)
    if value ne 0 then
        if IsDefined(Counts, key) then
            Counts[key] +:= value;
        else
            Counts[key] := value;
        end if;
    end if;
    return;
end procedure;

CONST_LabelSortingFunc := func<x,y | Tuple(y)[1] - Tuple(x)[1]>; // High to low.

procedure CorrectCountsByInclusionExclusion(~ellipticCounts)
    sortedKeys := Sort(Setseq(Keys(ellipticCounts)), CONST_LabelSortingFunc);

    for key in sortedKeys do
        tup := Tuple(key);
        rho := tup[1];
        
        if IsPrime(rho) then continue; end if;
        divs := [d : d in Divisors(rho) | d ne 1 and d ne rho];

        // Subtract away anything lying lower in the key poset.
        for p in divs do
            rhop := rho div p;
            subLabel := <rhop> cat <Integers() ! tup[i] : i in [2..#tup]>;
            assert IsDefined(ellipticCounts, subLabel);
            ellipticCounts[subLabel] -:= ellipticCounts[key];
        end for;
    end for;

    return;
end procedure;

// Function above should be equivalent to the old code below.
/* for rho in Reverse(isoOrds) do */
/*     rho2 := rho div 2; */
/*     if IsPrime(rho2) then continue; end if; */
/*     divs := [d : d in Divisors(rho2) | */
/*              (d ne 1) and (rho2 div d) in Keys(ellipticCounts)]; */
/*     for p in divs do */
/*         rho2p := rho2 div p; */
/*         for rot in Keys(ellipticCounts[rho2]) do */

/*             // Get the corresponding rotation factor for g^p, which is just */
/*             // a reduction of the rotation factor of the original element */
/*             // mod the order. */
/*             Par := Integers(rho2p); */
/*             rotp := [Par ! (Integers() ! x) : x in rot]; */

/*             // Update the table element. */
/*             ellipticCounts[rho2p][rotp] -:= ellipticCounts[rho2][rot]; */

/*         end for; */
/*     end for; */
/* end for; */


////////////////////////////////////////////////////////////////////////////////
//
// Main functionality.
//
////////////////////////////////////////////////////////////////////////////////

intrinsic CountEllipticPoints(Gamma::GrpHilbert) -> Assoc
{Given a congruence subgroup `Gamma` (level, field, decoration data), return an associative
array with the number of elliptic points for Gamma by type. The result is returned as an 
associative array of associative arrays. The keys of the first are orders of the isotropy 
groups. The keys of the second are the rotation factors. The values are the number of points 
with the given rotation factor.}

    if assigned Gamma`CountEllipticPoints then
        return Gamma`CountEllipticPoints;
    end if;

    // The algorithm is based on page 739 of "Quaternion Algebra, Voight".
    // Essentially, we count optimal embeddings of the order generated by the
    // isotropy group of the elliptic point into Gamma, up to conjugation.
    //
    // In the notation of JV, the number of embeddings of S into O, up to conjugation
    // by Gamma is m(S, O; Gamma).

    F  := BaseField(Gamma);
    ZF := MaximalOrder(F);
    hF := ClassNumber(ZF);
    hFplus := NarrowClassNumber(F);

    dim := Degree(F); // Dimension of Hilbert modular variety.
    assert dim eq 2;

    ellipticCounts := AssociativeArray();
    ellipticCountsByOrder := AssociativeArray();

    isoOrds := PossibleIsotropyOrders(F);
    for rho in isoOrds do
        ell_order := ExactQuotient(rho, 2);
        listOfOrders := OrderTermData(Gamma, F, rho);
        
        for Srec in listOfOrders do
            S := Srec`Order;
            
            num_plus, num_minus := CountEllipticPoints(Gamma, Srec, hF, hFplus);
            rot_factor_plus, rot_factor_minus := RotationFactors(Srec`RotationElement, ell_order);

            // Update debug information
            ellipticCountsByOrder[S] := AssociativeArray();
            ellipticCountsByOrder[S][rot_factor_plus]  := num_plus;
            ellipticCountsByOrder[S][rot_factor_minus] := num_minus;

            // Update requested information
            UpdateCountArray(~ellipticCounts, rot_factor_plus, num_plus);
            UpdateCountArray(~ellipticCounts, rot_factor_minus, num_minus);
        end for;
    end for;

    // Any times there is a containment relation S^x/R^x < S'^x/R^x,
    // we overcount the contribution
    // from S, since an elliptic point of order 4 is also counted as a point of order 2.
    // 
    // Thus, we post-process the elliptic counts due to overcounting in the previous step.
    CorrectCountsByInclusionExclusion(~ellipticCounts);
        
    Gamma`CountEllipticPoints := ellipticCounts;
    return Gamma`CountEllipticPoints;
end intrinsic;


////////////////////////////////////////////////////////////////////////////////
//
// Conversion to format used by ChowRing
//
////////////////////////////////////////////////////////////////////////////////

// NOTE: This stuff is not used in the LuCant paper, but might come in handy later.

intrinsic _EllipticPointData0(G::GrpHilbert) -> Assoc
{Helper function for `EllipticPointData`.}
    Counts := CountEllipticPoints(G);

    // Do some post processing.
    Data := AssociativeArray();
    for order in Keys(Counts) do
        for factor in Keys(Counts[order]) do
            // Drop identically 0 entries.
            c := Counts[order][factor];
            if c ne 0 then
                rot := HMVRotationLabel(<order> cat <x : x in factor>);
                Data[rot] := c;
            end if;
        end for;
    end for;

    return Data;
end intrinsic;


////////////////////////////////////////////////////////////////////////////////
//
// Debug utilities.
//
////////////////////////////////////////////////////////////////////////////////

intrinsic JohnPicardNumberCode(Z_Kabs, Z_K, UK, mUK, Dq, dff) -> RngIntElt
{Copied from Shimura curves. Computes the picard number of the order with conductor
dff inside Z_K. This function is for debug use only.}

    assert Z_K.1 eq 1;
    CI := CoefficientIdeals(Z_K);
    Oqbas := Basis(CI[1]) cat [z*Z_K.2 : z in Basis(dff*CI[2])];
    Oqbas := ChangeUniverse(Oqbas, Z_Kabs);
    Oq := sub< Z_Kabs | Oqbas >;
    assert Index(Z_Kabs, Oq) eq Norm(dff);

    UOq, mUOq := UnitGroupAsSubgroup(Oq, Z_Kabs : UG := <UK, mUK>);
    // wOq := #TorsionSubgroup(UOq);
    hOq := 1/#quo<UK | [UK| mUOq(u) : u in Generators(UOq)]> * AbsoluteNorm(dff) *
             Product([1-UnramifiedSquareSymbol(Dq,pp[1])/
                  AbsoluteNorm(pp[1]) : pp in Factorization(dff)]);

    return hOq;
end intrinsic;

intrinsic OrderNormIndex(S::RngOrd) -> RngIntElt
{Returns the index of Nm(Pic(S)) inside the narrow ray class group of the base field.}
  S_abs := AbsoluteOrder(S);
  pic_S, pic_map := PicardGroup(S_abs);
  R := BaseRing(S);
  cg, cg_map := NarrowClassGroup(R);
  norm_im := sub< cg | [Norm(S!!(Denominator(pic_map(g))*pic_map(g))) @@ cg_map
                        : g in Generators(pic_S)]>;
  return Index(cg, norm_im);
end intrinsic;

intrinsic OrderNormIndexWithAL(S::RngOrd, N::RngOrdIdl) -> RngIntElt
{Returns the index of Nm(Pic(S)) inside the narrow ray class group of the base field.
We also need the group of sign changes generated by the Atkin-Lehner (AL) elements.

This function is for debug purposes only. Additionally, it is presently known to produce
incorrect results.}
  
  S_abs := AbsoluteOrder(S);
  R := BaseRing(S);
  F := NumberField(R);
  pic_S, pic_map := PicardGroup(S_abs);
  cg, cg_map := ClassGroup(R);

  // Squares and norms
  cg_sq := hom<cg -> cg | [2*g : g in Generators(cg)]>;
  ncg, ncg_map := NarrowClassGroup(R);
  norms := [Norm(S!!(Denominator(pic_map(g))*pic_map(g))) @@ ncg_map
            : g in Generators(pic_S)];

  ////////////
  // Hmm...Below does not really depend on S, aside from the norms.

  // Atkin-Lehner primes
  fac_N := Factorization(N);
  AL_primes := [fa[1] : fa in fac_N];

  // Setup split quaternion algebra and the natural order
  M2F := MatrixAlgebra(F,2);
  _, B, mat_map := IsQuaternionAlgebra(M2F);
  gens := [[1,0,0,0], [0,1,0,0], [0,0,0,1]];
  gens cat:= [[0,0,g,0] : g in Generators(N)];
  O := Order([mat_map(M2F ! g) : g in gens]);

  for i->p in AL_primes do
    // Find the Atkin-Lehner involution associated to the
    // prime p.
    e := fac_N[i][2];

    // According to John's book (Chapter 28.9), Atkin-Lehner involutions correspond
    // to elements in the Atkin-Lehner group, i.e., Idl(O)/Idl(R). These in turn
    // correspond to ideals in the order O.
    //
    // Example 28.9 plus some other stuff implies that
    //
    //    Idl(O)/Idl(R) ~ prod(p | N; ZZ/2ZZ).
    //
    // In other words, we are looking for ideals that have reduced norm (determinant)
    // equal to p. This gives us a generating set.

    // Construct a two-sided ideal corresponding to an Atkin-Lehner involution.
    // Seemingly, we try random global representatives until we get something of the
    // correct norm?
    gens := [];
    for t in Generators(N) do
      gens_p := Generators(p);
      for i in [1..#gens_p] do
        M := N div p^e;
        if (M ne 1*R) then
            while (gens_p[i] in M) do
                gens_p[i] +:= &+[Random([-10..10]) * g : g in gens_p
                                 | g ne gens_p[i]];
            end while;
        end if;
        pi := gens_p[i];
        q := pi^e;
        Q, piQ := quo<R | M>;
        is_invertible, x_im := IsInvertible(piQ(q));

        if is_invertible then
            x := x_im @@ piQ;
            Append(~gens, mat_map([q*x, 1, q^2*x-q, q]));
        end if;
      end for;
    end for;

    if IsEmpty(gens) then
        Append(~gens, B!1);
    end if;

    J := ideal< O | gens>;

    // If we weren't able to construct a two-sided ideal, just move on

    // assert (J eq lideal<O | gens>) and (J eq rideal<O | gens>);
    if not( (J eq lideal<O | gens>) and (J eq rideal<O | gens>)) then
        continue;
    end if;

    // Lifting the AL to a global element
    fraka := Norm(J);
    fraka_cl := fraka @@ cg_map;
    c_inv := cg_map(fraka_cl @@ cg_sq);
    c := c_inv^(-1);

    // Sanity checks.
    c_gens := [x*y : x in Generators(c), y in Generators(J)];
    cJ := ideal< O | c_gens>;

    assert (cJ eq lideal<O | c_gens>) and (cJ eq rideal<O | c_gens>);
    assert Norm(cJ) @@ cg_map eq cg!0;
    is_principal, alpha := IsPrincipal(cJ);
    assert is_principal;
    assert &and[alpha * g * alpha^(-1) in O : g in Generators(O)];

    // Update norm generator list
    Append(~norms, Norm(alpha) @@ ncg_map);
  end for;
  norm_im := sub< ncg | norms >;
  return Index(ncg, norm_im);
end intrinsic;


intrinsic AtkinLehnerIdealBasis(Gamma::GrpHilbert) -> Any
{Computes a set of generators for the Atkin-Lehner group associated to
Gamma_0(N).

This function is for debug purposes only. Additionally, it is presently known to produce
incorrect results.}

  // According to John's book (Chapter 28.9), Atkin-Lehner involutions correspond
  // to elements in the Atkin-Lehner group, i.e., Idl(O)/Idl(R). These in turn
  // correspond to ideals in the order O.
  //
  // Example 28.9 plus some other stuff implies that
  //
  //    Idl(O)/Idl(R) ~ prod(p | N; ZZ/2ZZ).
  //
  // In other words, we are looking for ideals that have reduced norm (determinant)
  // equal to p. This gives us a generating set.

  assert GammaType(Gamma) eq GAMMA_0_Type;

  F := BaseField(Gamma);
  N := Level(Gamma);
  R := MaximalOrder(F);
  cg, cg_map := ClassGroup(R);

  // Squares and norms
  cg_sq := hom<cg -> cg | [2*g : g in Generators(cg)]>;
  ncg, ncg_map := NarrowClassGroup(R);

  // Atkin-Lehner primes
  fac_N := Factorization(N);
  AL_primes := [fa[1] : fa in fac_N];

  // Setup split quaternion algebra and the natural order
  M2F := MatrixAlgebra(F,2);
  _, B, mat_map := IsQuaternionAlgebra(M2F);
  gens := [[1,0,0,0], [0,1,0,0], [0,0,0,1]];
  gens cat:= [[0,0,g,0] : g in Generators(N)];
  O := Order([mat_map(M2F ! g) : g in gens]);

  // NEW ALGORITHM IDEA
  // We want to generate random elements of Idl(O) until we get the correct
  // generators for Idl(O)/Idl(R).

  // while Blah do
  // 1. Generate random ideal

  // 2. Reduce it down (?)

  // 3. Inspect the norm and do some kind of echelonization.

  // 4. Repeat until we get a group of the right order.
  // end while

  for i->p in AL_primes do
    // Find the Atkin-Lehner involution associated to the
    // prime p.
    e := fac_N[i][2];

    // Construct a two-sided ideal corresponding to an Atkin-Lehner involution.
    // Seemingly, we try random global representatives until we get something of the
    // correct norm?
    gens := [];
    for t in Generators(N) do
      gens_p := Generators(p);
      for i in [1..#gens_p] do
        M := N div p^e;
        if (M ne 1*R) then
            while (gens_p[i] in M) do
                gens_p[i] +:= &+[Random([-10..10]) * g : g in gens_p
                                 | g ne gens_p[i]];
            end while;
        end if;
        pi := gens_p[i];
        q := pi^e;
        x := InverseMod(q, M);
        Append(~gens, mat_map([q*x, 1, q^2*x-q, q]));
      end for;
    end for;
    J := ideal< O | gens>;
    assert (J eq lideal<O | gens>) and (J eq rideal<O | gens>);

    // Lifting the AL to a global element
    fraka := Norm(J);
    fraka_cl := fraka @@ cg_map;
    c_inv := cg_map(fraka_cl @@ cg_sq);
    c := c_inv^(-1);

    // Sanity checks.
    c_gens := [x*y : x in Generators(c), y in Generators(J)];
    cJ := ideal< O | c_gens>;

    assert (cJ eq lideal<O | c_gens>) and (cJ eq rideal<O | c_gens>);
    assert Norm(cJ) @@ cg_map eq cg!0;
    is_principal, alpha := IsPrincipal(cJ);
    assert is_principal;
    assert &and[alpha * g * alpha^(-1) in O : g in Generators(O)];

    // Update norm generator list
    Append(~norms, Norm(alpha) @@ ncg_map);
  end for;

  return 0;
end intrinsic;
