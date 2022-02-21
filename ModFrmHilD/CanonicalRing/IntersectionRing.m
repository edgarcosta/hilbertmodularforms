/////////////////////////////////////////////////////
//////////// Intersection Ring Code  ////////////////
/////////////////////////////////////////////////////

/*
// TODO:
-- Chern numbers for Hilbert Modular Group
-- Chern numbers for Gamma commensurable with the Hilbert Modular Group (torsion-free/with torsion)
-- Implementation of the intersection ring.
*/

/////////////////////////////////////////////////////
//
//    Chow ring (Intersection Ring) Type
//
/////////////////////////////////////////////////////

declare type ChowRngHMS[ChowRngHMSElt];
declare attributes ChowRngHMS[ChowRngHMSElt] : CongruenceSubgroup, EllipticPointIndices, ParabolicPointIndices, MultiplicationTable, GradedComponents, Generators;
declare attributes ChowRngHMSElt : Parent, GradedComponents;

// The Chow ring of a Hilbert Modular surface:
//
// -- We store elements as a trio <Number, Vector, Vector>, according to the graded
//    structure of the Chow ring of a surface.
//
// -- In principle, we could have used a PolynomialRing/Ideal to encode the Chow ring.
//    However, there are many trivial relations that need to be included in the ideal,
//    and this will end up killing performance. Instead, we implement the multiplication
//    by hand using a (Sparse) multiplication table.
//
// -- We also keep track of blocks of indices corresponding to the resolution cycles of
//    the elliptic and quotient singularities. 
//


intrinsic IntersectionRing(Gamma::StupidCongruenceSubgroup) -> ChowRngHMS
{Computes the Chow ring of the Bailey-Borel compactification of the Hilbert Modular Surface.}
    return IntersectionRing(Gamma, Integers());
end intrinsic;

// TODO: Depending on the subgroup, there may be MANY different quotient singularities
//       and cusps to resolve. It may be a good idea to implement a "Diagonal" option
//       to compress all the singularities of the same type into a single intersection class.
//
intrinsic IntersectionRing(Gamma::StupidCongruenceSubgroup, BR::Rng) -> ChowRngHMS
{Computes the Chow ring of the Bailey-Borel compactification of the Hilbert Modular Surface.
with coefficients in BR.}

    R := New(ChowRngHMS);
    R`CongruenceSubgroup := Gamma;


    // Figure out the number of elliptic + parabolic points and the lengths of the
    // resolution cycles.


    //////////////
    // Elliptic Points
    
    // For elliptic points, the precision should be irrelevant.
    RR := RealField(20);
    EPData := EllipticPointData(Gamma);
    rawEllipticResolutionData := [];
    
    for singType in Keys(EllipticPointData(Gamma)) do

	// Massage the type so that <a,b> = <1, positive>
	stdForm := <singType[1], 1, (singType[3] + (1 - singType[2])) mod singType[1]>;

	// Compute the HJContinuedFraction
	head, tail, isPeriodicOrFinite := HJContinuedFraction(RR ! (stdForm[1]/stdForm[3]));
	assert isPeriodicOrFinite;
	
	localChernCoeffs := QuotientLocalChernCoefficients(singType, head cat tail);
	for i in [1..EPData[singType]] do
	    Append(~rawEllipticResolutionData, <head cat tail, localChernCoeffs>);
	end for;
    end for;

    //////////////
    // Parabolic Points

    rawParabolicResolutionData := [[1,2,3], [4,5,6]];

    //////////////
    // Assembly of main structures.

    //////////////////////
    // Set up the multiplication table.

    // The multiplication table is determined by the resolution cycles.

    M := _RawToIntersectionMatrix(BR, rawEllipticResolutionData, rawParabolicResolutionData);
    R`MultiplicationTable := M;
    D := Nrows(M)-2;

    //////////////////////
    // Set up the graded components.
    
    R0 := RSpace(BR, 1);

    // TODO: The indexing system should remember the types of the points involved.
    // R`EllipticPointIndices := [[2, 3], [4, 5]];
    // R`ParabolicPointIndices := [[6, 7, 8]];


    R1 := RSpace(BR, D);

    // The top component.
    R2 := RSpace(BR, 1);

    R`GradedComponents := <R0, R1, R2>;


    // Finally, Cache the generators, since I suspect users will use them often.
    R`Generators := [CreateElement(R, 0, R1.i, 0) : i in [1..D]];
    
    return R;
end intrinsic;


///// Hilferfunktionen ///

intrinsic _RawToIntersectionMatrix(BR::Rng, ellipticData, parabolicData) -> MtrxSprs
{Internal constructor for the intersection matrix.}

    if #ellipticData gt 0 then
	ned := &+[#cycles : cycles in ellipticData];
    else
	ned := 0;
    end if;

    if #parabolicData gt 0 then
	npd := &+[#cycles : cycles in parabolicData];
    else
	npd := 0;
    end if;
    
    D := 1 + ned + npd;
    
    // NOTE: We "store" multiplication values for the cross-degree terms.
    M := SparseMatrix(BR, D+2, D+2);

    // Encode multiplication by the point class.
    for i in [1..D+2] do
	M[i,1] := 1;
	M[1,i] := 1;
    end for;

    // Begin the shift counter
    shift := 2;

    ////////////////////
    // Populate elliptic resolution data.
    for resolutionData in ellipticData do

	// TODO: The resolution cycle for a quotient singularity might be a chain of lines,
	//       rather than a cycle.
	
	localCycle  := resolutionData[1];
	chernCoeffs := resolutionData[2];

	for i in [1..#localCycle-1] do
	    M[shift+i, shift+i] := -localCycle[i];
	    M[shift+i, shift+i+1] := 1;
	    M[shift+i+1, shift+i] := 1;
	end for;

	// Update the last row/column in the block.
	i := #localCycle;
	M[shift + i, shift + i] := -localCycle[i];

	if i gt 1 then
	    M[shift+1, shift + i]   := 1;
	    M[shift + i, shift + 1] := 1;
	end if;

	// Update the coefficients of the first Chern cycle using the local Chern
	// cycle data.

	// NOTE: These local Chern coefficients are often rational numbers! But the
	//       self-intersection will turn out to be an integer (because of reasons).
	for i in [1..#localCycle] do
	    M[2, shift+i] := chernCoeffs[i];
	    M[shift+i, 2] := chernCoeffs[i];
	end for;
	
	// Update the shift.
	shift +:= #localCycle;
    end for;

    /////////////////////
    // Populate parabolic resolution data.
    for localCycle in parabolicData do

	// NOTE: If there is only one cycle, you need to do something special.
	//       Thus, even though the code is identical to the above that might change.
	
	for i in [1..#localCycle-1] do
	    M[shift+i, shift+i] := -localCycle[i];
	    M[shift+i, shift+i+1] := 1;
	    M[shift+i+1, shift+i] := 1;
	end for;

	// Update the last row/column in the block.
	i := #localCycle;
	M[shift + i, shift + i] := -localCycle[i];

	if i gt 1 then
	    M[shift+1, shift + i]   := 1;
	    M[shift + i, shift + 1] := 1;
	end if;

	// Update the shift.
	shift +:= #localCycle;
    end for;


    // The very last thing to do is update the canonical class.

    
    // TODO: XXX: Actually implement this.

    // Yeah...it looks like on the singular HMS the Chern forms only define QQ-divisors.
    // damned stackiness.
    
    
    // Return.
    return M;
end intrinsic;

/* function _ExtractRawEllipticResolutionData() */
/*     return true; */
/* end function; */

/* function _ExtractRawParabolicResolutionData() */
/*     return true; */
/* end function; */


intrinsic QuotientLocalChernCoefficients(type::Tup, selfIntersectionNumbers::SeqEnum) -> SeqEnum
{}
    // NOTE: Figuring out the local Chern cycle is a little tricky, as it is actually
    //       a QQ-divisor! See [vdG, p. 64]. For the definition of the (li, mi), see
    //       [vdG, p. 53].

    // In order to compute the local Chern cycle, we need the coordinates of the points
    // on the lower convex hull associated to the (positive) exponents.

    n := type[1];
    assert type[2] eq 1;
    q := type[3] mod n;

    _, _, qpr := XGCD(n, q);

    assert (qpr*q) mod n eq 1;
    
    RM := VectorSpace(Rationals(), 2);
    C0 := RM ! [1,0];
    C1 := RM ! [qpr/n, 1/n];

    N := 10;
    
    c := selfIntersectionNumbers cat selfIntersectionNumbers;
    C := [C0, C1] cat [Zero(RM) : i in [2..#c-2]];

    // Choose `d` as in [vdG]. That is, the length of the continued fraction
    // expansion (plus one).
    d := #selfIntersectionNumbers;
    
    // Use the equation C[i] * ci = C[i+1] + C[i-1].
    for i in [1..d] do
	C[i+2] := c[i+1] * C[i+1] - C[i];
    end for;

    print C; // TODO: If the length of the resolution cycle is 1, need to truncate.
    
    // Now that we have the coordinates, we can return the list of  (li + mi - 1).
    // Note that the beginning and ending terms of the `C` don't correspond to curves
    // in the resolution cycle, but instead to "coordinate axes" of `G\CC^2`. These points
    // are necessarily equal to `(1,0)` and `(0,1)`, so cancel

    lst := [c[1] + c[2] - 1 : c in C];
    assert lst[1] eq 0 and lst[#lst] eq 0;
    assert #lst ge 3; //i.e., check the resolution cycle has at least one curve.
    return lst[2..#lst-1];
    
end intrinsic;

/////////////// attribute access ///////////////////////////////////

intrinsic BaseRing(R::ChowRngHMS) -> Rng
{}
    return BaseRing(GradedComponent(R, 0));
end intrinsic;

intrinsic GradedComponent(R::ChowRngHMS, i::RngIntElt) -> Any
{}
    return GradedComponents(R)[i+1];
end intrinsic;

intrinsic GradedComponents(R::ChowRngHMS) -> Any
{}
    return R`GradedComponents;
end intrinsic;

intrinsic CongruenceSubgroup(R::ChowRngHMS) -> Any
{}
    return R`CongruenceSubgroup;
end intrinsic;

intrinsic MultiplicationTable(R::ChowRngHMS) -> MtrxSprs
{}
    return R`MultiplicationTable;
end intrinsic;

intrinsic '.'(R::ChowRngHMS, i::RngIntElt) -> Any
{}
    // TODO: Check with other people if they find this inoffensive.
    if i eq 0 then
	return R ! 1;
    elif i eq Dimension(GradedComponent(R, 1)) + 1 then
	return TopForm(R);
    end if;
    
    return Generators(R)[i];
end intrinsic;

/////////// Basic functionality //////////////////////

intrinsic Print(R::ChowRngHMS)
{}
    print "Chow Ring of Hilbert Modular Surface with congruence subgroup:";
    print CongruenceSubgroup(R);
end intrinsic;


intrinsic 'eq'(R::ChowRngHMS, S::ChowRngHMS) -> BoolElt
{}
    return CongruenceSubgroup(R) eq CongruenceSubgroup(S);
end intrinsic;

intrinsic Basis(R::ChowRngHMS) -> SeqEnum
{Return the basis for the Chow ring as a ZZ-module.}
    return [R ! 1] cat Generators(R) cat [TopForm(R)];
end intrinsic;

intrinsic TopForm(R::ChowRngHMS) -> ChowRngHMSElt
{}
    return CreateElement(R, 0, 0, 1);
end intrinsic;

intrinsic Generators(R::ChowRngHMS) -> SeqEnum
{Return the generators for the Chow ring as a polynomial ring over ZZ. We identify H^0(X, ZZ) with constants.}
    return R`Generators;
end intrinsic;

// intrinsic EllipticResolutionCycles(R::ChowRngHMS) -> SeqEnum
// {Return a basis of all elliptic resolution cycles.

// EllipticResolutionCycles(R::ChowRngHMS, singType::Tuple) -> SeqEnum
// {Return the basis of resolution cycles over a quotient singularity of the given type.}

// EllipticResolutionCycles(R::ChowRngHMS, singType::Tuple, i::RngIntElt) -> SeqEnum
// {Return the basis of resolution cycles of the given type over the i-th point of that type.}

// NumberOfEllipticPoints(R::ChowRngHMS)
// {Return the number of elliptic points of Gamma.}

// NumberOfEllipticPoints(R::ChowRngHMS, singType::Tup) -> SeqEnum
// {Return the number of elliptic points of Gamma of the given type.}


// Tensor ring over ZZ.
intrinsic ChangeRing(R::ChowRngHMS, BR::Rng) -> ChowRngHMS
{You know what this does.}
    return IntersectionRing(R, BR);
end intrinsic;

intrinsic Zero(R::ChowRngHMS) -> ChowRngHMSElt
{}
    return CreateElement(R);
end intrinsic;

intrinsic One(R::ChowRngHMS) -> ChowRngHMSElt
{}
    return CreateElement(R, 1, 0, 0);
end intrinsic;

////////////// Element Type intrinsics /////////////

intrinsic CreateElement(R::ChowRngHMS) -> ChowRngHMSElt
{}
    return CreateElement(R, <Zero(V) : V in GradedComponents(R)>);
end intrinsic;

intrinsic CreateElement(R::ChowRngHMS, d1::RngElt, d2::RngElt, d3::RngElt) -> ChowRngHMSElt
{}
    if d2 ne 0 then
	error "If the second argument is a ring element, it must be 0.";
    end if;
        
    return CreateElement(R, d1, Zero(GradedComponent(R,1)), d3);
end intrinsic;


intrinsic CreateElement(R::ChowRngHMS, d1::RngElt, d2::ModTupRngElt, d3::RngElt) -> ChowRngHMSElt
{}
    R0 := GradedComponent(R, 0);
    R2 := GradedComponent(R, 2);
    
    return CreateElement(R, <R0.1 * d1, d2, R2.1 * d3>);
end intrinsic;

intrinsic CreateElement(R::ChowRngHMS, d1::ModTupRngElt, d2::ModTupRngElt, d3::ModTupRngElt) -> ChowRngHMSElt
{}
    return CreateElement(R, <d1, d2, d3>);
end intrinsic;


// Core constructor.
intrinsic CreateElement(R::ChowRngHMS, ds::Tup) -> ChowRngHMSElt
{}
    x := New(ChowRngHMSElt);
    x`Parent := R;

    xcom := <Zero(V) : V in GradedComponents(R)>;
    for i in [1..3] do
	xcom[i] := GradedComponent(R, i-1) ! ds[i];
    end for;
    x`GradedComponents := xcom;
    
    return x;
end intrinsic;


//////////////////// attribute access ///////////////////////

intrinsic Parent(y::ChowRngHMSElt) -> ChowRngHMS
{}
    return y`Parent;
end intrinsic;

intrinsic GradedComponents(y::ChowRngHMSElt) -> Tup
{Return the graded components of the element, starting with degree 0.}
    return y`GradedComponents;
end intrinsic;

intrinsic GradedComponent(y::ChowRngHMSElt, i::RngIntElt) -> Tup
{Return the graded components of the element, starting with degree 0.}
    return GradedComponents(y)[i+1];
end intrinsic;


//////////////////// Basic functionality ///////////////////////
intrinsic Print(y::ChowRngHMSElt)
{}
    print "Element of Chow Ring of Hilbert Modular Surface.";
    print "Graded Components:";
    print GradedComponents(y);
end intrinsic;

intrinsic BaseRing(y::ChowRngElt) -> Rng
{}
    return BaseRing(Parent(y));
end intrinsic;


intrinsic Coefficients(x::ChowRngHMSElt) -> SeqEnum
{Return the coefficients of x with respect to Basis(Parent(x)).}
    return &cat[Eltseq(xi) : xi in GradedComponents(x)];
end intrinsic;

intrinsic Coefficient(x::ChowRngHMSElt, i::RngIntElt) -> RngElt
{Return the i-th coeffcient of x with respect to the standard basis.}
    return Coefficients(x)[i];
end intrinsic;

intrinsic Coefficient(x::ChowRngHMSElt, b::ChowRngHMSElt) -> RngElt
{If b is an element of the standard basis for the Chow ring, return the coefficient
of b within the element x = Sum(ci * bi).}

    assert Parent(x) eq Parent(b);
    ind := Index(Basis(Parent(x)), b);

    if ind eq 0 then
	error "Second argument is not in the standard basis.";
    end if;
    return Coefficients(x)[ind];
end intrinsic;

intrinsic 'eq'(x::ChowRngHMSElt, y::ChowRngHMSElt) -> BoolElt
{}
    if Parent(x) ne Parent(y) then
	return false;
    end if;
    
    for i in [0..2] do
	if GradedComponent(x, i) ne GradedComponent(y, i) then
	    return false;
	end if;
    end for;

    return true;
end intrinsic;

intrinsic '+'(x::ChowRngHMSElt, y::ChowRngHMSElt) -> ChowRngHMSElt
{}
    R := Parent(x);
    assert R eq Parent(y);
    
    xcom := GradedComponents(x);
    ycom := GradedComponents(y);

    return CreateElement(R, <xcom[i] + ycom[i] : i in [1..3]>);
end intrinsic;

intrinsic '+'(x::RngElt, y::ChowRngHMSElt) -> ChowRngHMSElt
{}
    R := Parent(y);
    R0 := GradedComponent(R, 0);
    assert Parent(x) eq BaseRing(R);
    
    ycom := GradedComponents(y);
    newcom := <ycom[1] + x*R0.1, ycom[2], ycom[3]>;

    return CreateElement(R, newcom);
end intrinsic;

intrinsic '+'(y::ChowRngHMSElt, x::RngElt) -> ChowRngHMSElt
{}
    return x + y;
end intrinsic;



intrinsic '-'(x::ChowRngHMSElt, y::ChowRngHMSElt) -> ChowRngHMSElt
{}
    R := Parent(x);
    assert R eq Parent(y);
    
    xcom := GradedComponents(x);
    mocx := GradedComponents(y);

    return CreateElement(R, <xcom[i] - mocx[i] : i in [1..3]>);
end intrinsic;

intrinsic '-'(x::RngElt, y::ChowRngHMSElt) -> ChowRngHMSElt
{}
    R := Parent(y);
    R0 := GradedComponent(R, 0);
    assert Parent(x) eq BaseRing(R);

    ycom := GradedComponents(y);
    newcom := <x*R0.1 - ycom[1], -ycom[2], -ycom[3]>;

    return CreateElement(R, newcom);
end intrinsic;

// Subtraction is implemented twice so that a new element is only created once.
intrinsic '-'(y::ChowRngHMSElt, x::RngElt) -> ChowRngHMSElt
{}
    R := Parent(y);
    R0 := GradedComponent(R, 0);
    assert Parent(x) eq BaseRing(R);

    ycom := GradedComponents(y);
    newcom := <ycom[1] - x*R0.1, ycom[2], ycom[3]>;

    return CreateElement(R, ycom);
end intrinsic;


intrinsic '-'(x::ChowRngHMSElt) -> ChowRngHMSElt
{}
    R := Parent(x);    
    xcom := GradedComponents(x);
    return CreateElement(R, <-xcom[i] : i in [1..3]>);
end intrinsic;


intrinsic '*'(x::RngElt, y::ChowRngHMSElt) -> ChowRngHMSElt
{}
    R := Parent(x);
    assert R eq BaseRing(Parent(y));

    ycom := GradedComponents(y);
    return CreateElement(Parent(y), <x * ycom[i] : i in [1..3]>);
end intrinsic;

intrinsic '*'(y::ChowRngHMSElt, x::RngElt) -> ChowRngHMSElt
{}
    return x * y;
end intrinsic;

intrinsic '*'(x::ChowRngHMSElt, y::ChowRngHMSElt) -> ChowRngHMSElt
{}
    R := Parent(x);
    assert Parent(x) eq Parent(y);

    // Unpack
    x0 := GradedComponent(x, 0)[1];
    x1 := GradedComponent(x, 1);
    x2 := GradedComponent(x, 2);
    
    y0 := GradedComponent(y, 0)[1];
    y1 := GradedComponent(y, 1);
    y2 := GradedComponent(y, 2);

    // Degree 0
    z0 := x0*y0;
    
    // Degree 1
    z1 := x0 * GradedComponent(y, 1) + GradedComponent(x, 1) * y0;
    
    // Degree 2
    R1 := GradedComponent(R, 1);
    M := MultiplicationTable(R); // This also contains the degree 0, degree 2 pieces.
    z2 := x2[1] * y0 + x0 * y2[1];

    for i in [1..Dimension(R1)] do
	for j in [1..Dimension(R1)] do
	    z2 +:= x1[i] * M[i+1,j+1] * y1[j];
	end for;
    end for;
        
    return CreateElement(R, z0, z1, z2);
end intrinsic;

intrinsic '^'(y::ChowRngHMSElt, n::RngElt) -> ChowRngHMSElt
{}

    if n gt 2 then
	R := Parent(y);
	R0 := GradedComponent(R, 0);
	y1 := GradedComponent(y, 1);
	y2 := GradedComponent(y, 2);

	z := CreateElement(R, Zero(R0), y1, y2);
	a := GradedComponent(y, 0)[1];

	inv := (a*n)*z + (a^2 * Binomial(n, 2)) * z^2;
	inv`GradedComponents[1] := a*R0.1;
	return inv;

    elif n lt 0 then
	boo, u := IsInvertible(y);
	if not boo then
	    error "Inversion not implemented in the Chow Ring.";
	else
	    return u^(-n);
	end if;
    end if;

    case n:
    when 0:
	if y eq 0 then
	    error "Cannot compute 0^0 in the Chow ring.";
	else
	    return One(R);
	end if;
    when 1:
	return y;
    when 2:
	return y*y;
    end case;
end intrinsic;


intrinsic IsInvertible(x::ChowRngHMSElt) -> BoolElt, ChowRngHMSElt
{}
    boo, u := IsInvertible(GradedComponent(x, 0)[1]);
    if not boo then return false; end if;

    R := Parent(x);
    z := u * x - One(R);
    return true, u*(One(R) - z + z^2);
end intrinsic;
    

intrinsic IsCoercible(X::ChowRngHMS, y::.) -> BoolElt, .
{Return whether y is coercible into X and the result if so}

    if Type(y) eq RngIntElt then
	return true, CreateElement(X, 1, 0, 0);
    end if;

    if Type(y) eq ChowRngHMSElt and Parent(y) eq X then
	return true, y;
    end if;

    return false, "Illegal coercion.";
end intrinsic;


////////////// Greater functionality ////////////////

// TODO: Navigation of the classes in the Chow ring.
intrinsic BasisCycleInformation(x::ChowRngHMSElt) -> BoolElt, MonStgElt, RngIntElt
{}
    return false, "quotient", 1;
end intrinsic;

/////////////////////////////////////////////////////
//
//    Dispatch for Number Field Input.
//
/////////////////////////////////////////////////////

intrinsic ChernNumbersOfMinimalResolution(F::FldNum) -> SeqEnum
{Returns a tuple <c1^2, c2> corresponding to the Chern numbers of the 
minimal resolution of the Hilbert Modular Surface for the Hilbert Modular Group.}
    return ChernNumbersOfMinimalResolution(F, 1*RingOfIntegers(F));
end intrinsic;

intrinsic ChernNumber(F::FldNum, n::RngIntElt) -> RngIntElt
{Returns the ith Chern number of the
minimal resolution of the Hilbert Modular Surface for the Hilbert Modular Group.}
    return ChernNumbersOfMinimalResolution(F, 1*RingOfIntegers(F));
end intrinsic;

intrinsic IntersectionRing(F::FldNum) -> Any
{Computes the Cohomology ring of the Bailey-Borel compactification of the Hilbert Modular Surface.}
        return IntersectionRing(F, 1*RingOfIntegers(F));
end intrinsic;

intrinsic IntersectionRingOfCuspidalResolution(F::FldNum) -> Any
{Computes the Cohomology ring of the surface resolving the cusp singularities of the Hilbert Modular Surface.}
    return IntersectionRingOfCuspidalResolution(F, 1*RingOfIntegers(F));
end intrinsic;

intrinsic IntersectionRingOfMinimalResolution(F::FldNum) -> Any
{Computes the Cohomology ring of the minimal resolution of the singularities of the Hilbert Modular Surface.}
    return IntersectionRingOfMinimalResolution(F, 1*RingOfIntegers(F));
end intrinsic;


intrinsic VolumeOfFundamentalDomain(F::FldNum) -> Any
{Return the Volume of the fundamendal domain of the (non-compact) Hilbert Modular Surface.}
    return VolumeOfFundamentalDomain(F, 1*RingOfIntegers(F));
end intrinsic;

/////////////////////////////////////////////////////
//
//    Dispatch for Number Field Input plus level.
//
/////////////////////////////////////////////////////

intrinsic ChernNumbersOfMinimalResolution(F::FldNum, N::RngOrdIdeal) -> SeqEnum
{Returns a tuple <c1^2, c2> corresponding to the Chern numbers of the 
minimal resolution of the Hilbert Modular Surface for the Hilbert Modular Group.}
    Gamma := StupidCongruenceSubgroup(F, N);
    return ChernNumbersOfMinimalResolution(Gamma);
end intrinsic;

intrinsic IntersectionRing(F::FldNum, N::RngOrdIdeal) -> Any
{Computes the Cohomology ring of the Bailey-Borel compactification of the Hilbert Modular Surface.}
    Gamma := StupidCongruenceSubgroup(F, N);
    return IntersectionRing(Gamma);
end intrinsic;

intrinsic IntersectionRingOfCuspidalResolution(F::FldNum, N::RngOrdIdeal) -> Any
{Computes the Cohomology ring of the surface resolving the cusp singularities of the Hilbert Modular Surface.}
    Gamma := StupidCongruenceSubgroup(F, N);
    return IntersectionRingOfCuspidalResolution(Gamma);
end intrinsic;

intrinsic IntersectionRingOfMinimalResolution(F::FldNum, N::RngOrdIdeal) -> Any
{Computes the Cohomology ring of the minimal resolution of the singularities of the Hilbert Modular Surface.}
    Gamma := StupidCongruenceSubgroup(F, N);
    return IntersectionRingOfMinimalResolution(Gamma);
end intrinsic;


intrinsic VolumeOfFundamentalDomain(F::FldNum, N::RngOrdIdeal) -> Any
{Return the Volume of the fundamendal domain of the (non-compact) Hilbert Modular Surface.}
    Gamma := StupidCongruenceSubgroup(F, N);
    return VolumeOfFundamentalDomain(Gamma);
end intrinsic;


/////////////////////////////////////////////////////
//
//    Dispatch for Graded Ring of HMF Input.
//
/////////////////////////////////////////////////////

// NOTE: Because the ModFrmHilDGRng does not keep track of a level, we
//       insist that the user specifies this information in the constructor.

intrinsic ChernNumbersOfMinimalResolution(M::ModFrmHilDGRng, N::RngOrdIdl) -> SeqEnum
{Returns a tuple <c1^2, c2> corresponding to the Chern numbers of the 
minimal resolution of the Hilbert Modular Surface for the Hilbert Modular Group.}
    Gamma := StupidCongruenceSubgroup(Field(M), N);
    return ChernNumbersOfMinimalResolution(Gamma);
end intrinsic;

intrinsic IntersectionRing(M::ModFrmHilDGRng, N::RngOrdIdl) -> Any
{Computes the Cohomology ring of the Bailey-Borel compactification of the Hilbert Modular Surface.}
    error "Not Implemented.";
end intrinsic;

intrinsic IntersectionRingOfCuspidalResolution(M::ModFrmHilDGRng, N::RngOrdIdl) -> Any
{Computes the Cohomology ring of the surface resolving the cusp singularities of the Hilbert Modular Surface.}
    error "Not Implemented.";
end intrinsic;

intrinsic IntersectionRingOfMinimalResolution(M::ModFrmHilDGRng, N::RngOrdIdl) -> Any
{Computes the Cohomology ring of the minimal resolution of the singularities of the Hilbert Modular Surface.}
    error "Not Implemented.";
end intrinsic;


intrinsic VolumeOfFundamentalDomain(M::ModFrmHilDGRng, N::RngOrdIdl) -> Any
{Return the Volume of the fundamendal domain of the (non-compact) Hilbert Modular Surface.}
    Gamma := StupidCongruenceSubgroup(Field(M), N);
    return VolumeOfFundamentalDomain(Gamma);
end intrinsic;


/////////////////////////////////////////////////////
//
//    General Hilbert Modular Surface code.
//
/////////////////////////////////////////////////////


intrinsic ChernNumbersOfMinimalResolution(Gamma::StupidCongruenceSubgroup) -> SeqEnum
{Returns a tuple <c1^2, c2> corresponding to the Chern numbers of the 
minimal resolution of the Hilbert Modular Surface for the Hilbert Modular Group.}

  error "Not implemented.";
  // For now, let us assume the groups is torsion-free.

  // We use the description of the Chern Numbers of a Hilbert Modular Surface
  // from van der Geer, Theorem IV.2.5 (page 64). To expand on this a bit,
  // The theorem essentially states that the Chern numbers for the minimal
  // resolution of singularities are comprised of
  //
  // -- a volume term, which can be computed from the volume of the Hilbert Modular Group,
  // -- exceptional cycles from the cusp, and
  // -- exceptional cycles from the quotient singularities (when Gamma has torsion).
  //
  // The volume term happens to be an Euler number of the (non-compact) fundamental domain,
  // plus correction term for the quotient singularities and (zero-dimensional) boundary.

  ///////////////////////////////////////////////
  // Computing the Euler number (c2)
  
  // 1. Determine the Volume of Gamma.
  volume := VolumeOfFundamentalDomain(Gamma);

  
  // 2. Determine the branch points of the natural cover of X_{Gamma_K}.
  // 3. Apply Riemann-Hurwitz (Theorem IV.1.2, vdG)
  // 4. Add "1" for each cusp.
  
  secondChernNumber := volume + NumberOfCusps(Gamma);

  ///////////////////////////////////////////////
  // Computing c1^2.

  // 1. Compute 2*Volume, as above.
  // 2. Compute the b_k for the resolution cycles at the cusp.
  // 3. Add (2-b_k) for each cusp.

  // TODO: Sam is writing a function for computing the resolution cycles. 

  // theCusps := SamIsWorkingOnThis();
  // bks := [SomeFunction(cc) : cc in theCusps];

  firstChernNumber := -100;
  
  //////////////
  // Adding correction terms for the quotient singularities.

  // 1. Compute the torsion in Gamma.
  // 2. Compute the correction terms appearing in Theorem 2.5.
  if not IsTorsionFree(Gamma) then
      // Placeholder.
      C1TorsionCorrectionTerms := -100;
      C2TorsionCorrectionTerms := -100;
      
      firstChernNumber +:= C1TorsionCorrectionTerms;
      secondChernNumber +:= C2TorsionCorrectionTerms;

      error "Not Implemented when Gamma has torsion.";
  end if;
      
  return <"Not Implemented", secondChernNumber>;
end intrinsic;

intrinsic ResolutionCycleData(tup) -> Any
{Given a tuple describing the type of a quotient singularity, return the
cycle of curves in the resolution together with the intersection matrix.}
    error "Not Implemented.";

    // Here, assuming that tup[2] = 1, we basically
    // compute the Hirzebruch-Young continued fraction expansion for n/tup[3].
    // (Or n/(n - tup[3]), to ensure that we take the continued fraction expansion of something positive.)
    return "";
end intrinsic;

// TODO: Move the IntersectionRing intrinsic down here after done with the creation logic.
intrinsic IntersectionRingOfCuspidalResolution(Gamma::StupidCongruenceSubgroup) -> Any
{Computes the Cohomology ring of the surface resolving the cusp singularities of the Hilbert Modular Surface.}
    error "Not Implemented.";
end intrinsic;

intrinsic IntersectionRingOfMinimalResolution(Gamma::StupidCongruenceSubgroup) -> Any
{Computes the Cohomology ring of the minimal resolution of the singularities of the Hilbert Modular Surface.}
    error "Not Implemented.";
end intrinsic;


intrinsic VolumeOfFundamentalDomain(Gamma::StupidCongruenceSubgroup) -> Any
{Return the Volume of the fundamendal domain of the (non-compact) Hilbert Modular Surface.}
    return Index(Gamma) * Evaluate(DedekindZeta(Field(Gamma)), -1);
end intrinsic;


/////////////////////////////////////////////////////////////////////////////////
//
// Alias
//
/////////////////////////////////////////////////////////////////////////////////

intrinsic ChowRing(Gamma) -> ChowRngHMS
{}
    return IntersectionRing(Gamma);
end intrinsic;


/////////////////////////////////////////////////////////////////////////////////
//
// Test Intersection Ring
//
/////////////////////////////////////////////////////////////////////////////////

