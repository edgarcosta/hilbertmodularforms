
//////////////////////////////////////////////////////

///////////// Hibert Series/Dimension Formula ////////

//////////////////////////////////////////////////////

// This allows us to compute the dimension without loading the basis for the entire space.
// Currently only implemented for real quadratic fields with Discriminant D <41. If you want
// higher discriminants or cubic fields just ask Ben.
// Formula in Thomas, Vasquez - Rings of Hilbert Modular Forms pg 147-148 Theorem 3.4,
// Cubic fields pg 149-151


/*
 * DEPRECATED: see A3 and ArithmeticGenus
// List of Coefficients for A3 and the Arithmetic Genus. From Hirzebruch - Hilbert Modular
// Surfaces (A3 on pg. 198-200, chi on pg 239). This comes from Prestel Die Elliptischen
// fixpunte der hilbertshen Modulgruppen.
intrinsic TableA3andGenus(D::RngIntElt) -> List
{Takes a Fundamental Discriminant D and returns the genus and value for a3}

    require D lt 42: "Tables not implemented for discriminant > 42.";

    T := [
    [2,3,5,6,7,10,11,13,14,15,17,19,21,22,23,26,29,30,31,33,34,35,37,38,39,41],
	  [2,2,2,3,4, 4, 4, 4, 4, 6, 2, 4, 5, 8, 8, 4, 6,10, 4, 3, 4, 8, 8, 8,10, 2],
	  [1,1,1,1,1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 3, 5, 2, 3, 4, 1, 6, 4, 2, 6, 7, 2]];

    d,e := SquareFree(D);
    i := Index(T[1],d);

    a3 := T[3][i];
    Genus := T[2][i];

    return a3, Genus;
end intrinsic;
*/


intrinsic A3(D::RngIntElt) -> RngIntElt
{ a3 associated to Q(sqrt(-d)) }
    if not IsFundamentalDiscriminant(D) then
        D := Discriminant(Integers(QuadraticField(D)));
    end if;

    if D mod 3 ne 0 then
        return ClassNumber(-3*D);
    else
        d := D div 3;
        h := ClassNumber(-d);
        if d mod 3 eq 1 then
            return 5*h;
        elif d mod 3 eq 2 then
            return 3*h;
        end if;
    end if;
end intrinsic;


// Only implemented for certain quadratic fields. Formula in Thomas, Vasquez - Rings of Hilbert
// Modular Forms pg 147-148 Theorem 3.4
// Generating function for the dimension of the space of HMFs according to weight k
// Input: M = HMFspace
// Output: G = Hilbert Series (i.e. generating function for dimensions)
intrinsic HilbertSeriesVasquez(K::FldNum) -> FldFunRatUElt
{Use the Formulas from Vasquez to compute the Hilbert series for the space of Hilbert modular
forms (with respect to the full Hilbert Modular Group).}

    require #NarrowClassGroup(K) eq 1: "the formula only works for trivial narrow class group";
    Disc := Discriminant(Integers(K));
    P<x> := FunctionField(Rationals());


    h := ClassNumber(K); // this is 1


    zeta := DedekindZetaExact(K, -1);
    chi := ArithmeticGenus(K);
    a3 := A3(Disc);
    h := ClassNumber(K);

    // Discriminant 5 is a special case.
    if Disc eq 5 then
	B := (1+x^20);
	return (1+x^20)*(1-x^2)^(-1)*(1-x^6)^(-1)*(1-x^(10))^(-1);
    end if;

    // Computing sd from formula 2.13 on pg 145.
    if Disc mod 3 ne 0 then
	sD := 1/6;
    elif Disc gt 12 and (Disc mod 9) eq 3 then
	sD := 4/15;
    elif Disc eq 12 or (Disc mod 9) eq 6 then
	sD := 1/3;
    else
	error "Not implemented when Discriminant is:", Disc;
    end if;

    B0 := 1;
    B1 := chi + h - 3;
    B2 := 4*zeta - chi - sD*a3 - h + 3;
    B3 := 4*zeta + 2*sD*a3 - 2;

    B := B0 + B1*x^2 + B2*x^4 + B3*x^6 + B2*x^8 + B1*x^10 + B0*x^12;
    G := B*(1-x^2)^(-2)*(1-x^6)^(-1);

    return G;
end intrinsic;

intrinsic testHilbertSeriesVasquez() -> BoolElt
{Consistency checks for HilbertSeriesVasquez.}

    K   := QuadraticField(21);
    h   := ClassNumber(K);
    a3  := 5;    // Number of elliptic points of order 3 on the HMS.
    s   := 4/15; // Vasquez's mysterious constant.
    chi := 1;    // Arithmetic genus of the HMS.
    zm1 := DedekindZetaExact(K, -1);

    cuspFormDims := [0,
		     chi - 1,
		     4 * zm1 + 1 - a3 * s,
		     12 * zm1 + 1,
		     24 * zm1 + 1,
		     40 * zm1 + 1 - a3 * s,
		     60*zm1 + 1];

    MkDims := [1] cat [h + cuspFormDims[i] : i in [2..#cuspFormDims]];

    // Compare coefficients.
    PP<t> := PowerSeriesRing(Rationals(), 20);
    hilb  := PP ! HilbertSeriesVasquez(K);

    evenCoeffs := [c : c in Coefficients(hilb)[1 .. 2*#MkDims by 2]];
    comp := [MkDims[i] - evenCoeffs[i] : i in [1..#MkDims]];

    return &and [c eq 0 : c in comp];
end intrinsic;


intrinsic HilbertSeriesVdG(Gamma::GrpHilbert) -> FldFunRatUElt
{Closed-form Hilbert series for a single component of a Hilbert modular surface,
using Proposition VIII.1.1 of van der Geer, Hilbert Modular Surfaces.
Requires level 1 and Gamma0 type.  The variable t corresponds to even weight,
so the coefficient of t^m is the dimension of weight-2m forms.}

    F := BaseField(Gamma);
    ZF := Integers(F);
    D := Discriminant(ZF);

    require Degree(F) eq 2 : "Only implemented for real quadratic fields";
    require Norm(Level(Gamma)) eq 1 : "Only implemented for level 1";
    require GammaType(Gamma) eq "Gamma0" : "Only implemented for Gamma0";

    R<t> := FunctionField(Rationals());

    // D = 5 is a special case: order-5 elliptic points break the
    // period-3 structure assumed by the generic formula.
    if D eq 5 then
        return (1 + t^10) * (1-t)^(-1) * (1-t^3)^(-1) * (1-t^5)^(-1);
    end if;

    // Per-component invariants
    chi := ArithmeticGenus(Gamma);
    h := NumberOfCusps(Gamma);
    vol := VolumeOfFundamentalDomain(Gamma);

    // tau_ot = (1/3)*a_3^+ for the component, extracted from the
    // weight-4 cusp form dimension via [vdG IV.4]
    // Coerce to rationals since DimensionOfCuspForms may live in a cyclotomic field.
    tau_ot := Rationals() ! (2*vol + chi - DimensionOfCuspForms(Gamma, 4));

    b0 := 1;
    b1 := Rationals() ! (chi + h - 3);
    b2 := Rationals() ! (2*vol - chi - tau_ot - h + 3);
    b3 := Rationals() ! (2*vol + 2*tau_ot - 2);

    B := b0 + b1*t + b2*t^2 + b3*t^3 + b2*t^4 + b1*t^5 + b0*t^6;
    return B * (1-t)^(-2) * (1-t^3)^(-1);

end intrinsic;

intrinsic HilbertSeriesVdG(F::FldNum) -> SeqEnum[FldFunRatUElt]
{Closed-form Hilbert series for each component of the Hilbert modular surface
over the real quadratic field F at level 1, using Proposition VIII.1.1 of
van der Geer, Hilbert Modular Surfaces.  Returns a sequence indexed by
narrow class group representatives.}

    require Degree(F) eq 2 : "Only implemented for real quadratic fields";
    ZF := Integers(F);
    NCl, mp := NarrowClassGroup(F);
    return [HilbertSeriesVdG(CongruenceSubgroup("GL+", "Gamma0", F, 1*ZF, mp(el)))
            : el in NCl];

end intrinsic;


intrinsic HilbertSeriesLevelOne(M::ModFrmHilDGRng) -> FldFunRatUElt
{Returns the dimension of the space of Hilbert Modular Forms of weight `k` and level `(1)`.}
    return HilbertSeriesVasquez(BaseField(M));
end intrinsic;

intrinsic HilbertSeries(F::FldNum, level::RngOrdIdl) -> FldFunRatUElt
{Return the Hilbert series for the space of Hilbert Modular Forms of weight `k` with respect to
the congruence subgroup `G`.}
    if (NarrowClassNumber(F) eq 1) and (Norm(level) eq 1) then
        return HilbertSeriesVasquez(F);
    end if;
    M := GradedRingOfHMFs(F, 1);
    M2 := HMFSpace(M, level, [2,2]);
    HC := HilbertSeriesCusp(M, level);
    R<T> := Parent(HC);
    HE := EisensteinDimension(M2)*T^2/(1-T^2);
    H := HC + HE + NarrowClassNumber(M);
    return H;
end intrinsic;


intrinsic HilbertSeriesCusp(F::FldNum, level::RngOrdIdl : prec:=false) -> FldFunRatUElt
{Return the Hilbert series for the space of cusp Hilbert Modular Forms of weight `k` with respect to
the congruence subgroup `G`.}
    M := GradedRingOfHMFs(F, 1);
    return HilbertSeriesCusp(M, level : prec:=prec);
end intrinsic;


// Dimension of the space of HMFs of weight k
// Input: M = HMFspace
// Input: k weight
// Output: dim(M(k))

// Old function. Mk now carries its own dimension around; go ahead and ask for it.
/*
intrinsic Dimension(Mk::ModFrmHilD) -> RngIntElt
{Returns the dimension of the space of Hilbert Modular Forms of weight k}
	M := Parent(Mk); k := Weight(Mk)[2];
	assert k mod 2 eq 0; assert Level(Mk) eq 1*Integers(M); // Trivial level and even weight.
	DimGen := DimensionGeneratingFunction(M);
	dim := Round(Coefficient(DimGen, k));
	return dim;
end intrinsic;
*/
