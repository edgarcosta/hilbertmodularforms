/////////////////////////////////////////////////////
//////////// Intersection Ring Code  ////////////////
/////////////////////////////////////////////////////

/////////////////////////////////////////////////////
//
//    Singular Point labels
//
/////////////////////////////////////////////////////

declare type StupidSingularPointHMS;
declare attributes StupidSingularPointHMS : Parent, Point, SingularityType, SingularityInfo, ID;

// TODO: Once actually correct data is attached to singular points,
//       we can remove this.
declare type GlobalSingularPointHMSCounter;
declare attributes GlobalSingularPointHMSCounter : Count;

GlobalSingularPointHMSCount := New(GlobalSingularPointHMSCounter);
GlobalSingularPointHMSCount`Count := 0;

intrinsic GetSingularPointHMSCount() -> RngIntElt
{}
    return GlobalSingularPointHMSCount`Count;
end intrinsic;

intrinsic Increment(globalvar::GlobalSingularPointHMSCounter)
{}
    globalvar`Count +:= 1;
    return;
end intrinsic;

///////////////////// Singular Point HMS intrinsics /////////////////////

intrinsic SingularPointHMS(typename::MonStgElt, info::Tup) -> StupidSingularPointHMS
{}
    acceptableQuotientNames := ["Elliptic", "Quotient", "Orbifold"];
    acceptableCuspidalNames := ["Cusp", "Cuspidal", "Parabolic"];

    if typename in acceptableQuotientNames then
	singname := "Quotient";
    elif typename in acceptableCuspidalNames then
	singname := "Cusp";
    else
	error "Singularity type: `", typename, "` not regconized for HMS singularity.";
    end if;

    p := New(StupidSingularPointHMS);
    p`SingularityType := singname;
    p`SingularityInfo := info;
    p`Point := "Fake Coordinates";
    p`ID := GlobalSingularPointHMSCount`Count;
    Increment(GlobalSingularPointHMSCount);
    return p;
end intrinsic;

intrinsic SingularPointHMS(typename::MonStgElt, info::Tup, point) -> StupidSingularPointHMS
{}
    p := SingularPointHMS(typename, info);
    p`Point := point;
    return p;
end intrinsic;

intrinsic 'eq'(x::StupidSingularPointHMS, y::StupidSingularPointHMS) -> BoolElt
{}
    // TODO: Once we assign parents to such things, we should check it.
    // TODO: Once the data structure of a singular point is determined, the `eq` function
    //       should change to reflect it.
    return x`ID eq y`ID;
end intrinsic;

intrinsic Print(p::StupidSingularPointHMS)
{}
    singType := p`SingularityType;

    if singType eq "Quotient" then
	msgpart := Sprintf("%o singularity of type %o", p`SingularityType, p`SingularityInfo);

    elif singType eq "Cusp" then
	msgpart := Sprintf("%o", p`SingularityType);
    else
	print singType;
    end if;

    print "Representative of", msgpart, "of Hilbert Modular Surface.";
    print "With object ID: ", p`ID;
    return;
end intrinsic;

/////////////////////////////////////////////////////
//
//    Chow ring (Intersection Ring) Type
//
/////////////////////////////////////////////////////

declare type ChowRngHMS[ChowRngHMSElt];
declare attributes ChowRngHMS[ChowRngHMSElt] : CongruenceSubgroup, ResolutionCycles, MultiplicationTable, GradedComponents, Generators, GeneratorInfo;
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
//    the elliptic and quotient singularities. `ResolutionCycles` is an AssociativeArray whose
//    keys are singular points and whose values are the resolution cycles over that point.
//
// -- Additionally, we cache the reverse map from Generators to the associated singular point.
//    This is the AssociativeArray `GeneratorInfo`.
//

/////////////// attribute access ///////////////////////////////////

intrinsic BaseRing(R::ChowRngHMS) -> Rng
{}
    return BaseRing(GradedComponent(R, 0));
end intrinsic;

intrinsic GradedComponent(R::ChowRngHMS, i::RngIntElt) -> ModTupRng
{}
    return GradedComponents(R)[i+1];
end intrinsic;

intrinsic GradedComponents(R::ChowRngHMS) -> Tup
{}
    return R`GradedComponents;
end intrinsic;

intrinsic CongruenceSubgroup(R::ChowRngHMS) -> GrpHilbert
{}
    return R`CongruenceSubgroup;
end intrinsic;

intrinsic MultiplicationTable(R::ChowRngHMS) -> MtrxSprs
{Return a table encoding multiplication in the Chow ring. The first row/column of the table
corresponds to the trivial class, and the last row/column corresponds to the basis degree 2 class.}
    return R`MultiplicationTable;
end intrinsic;

intrinsic '.'(R::ChowRngHMS, i::RngIntElt) -> ChowRngHMSElt
{}
    if i notin [1..Ngens(R)] then
	n := Ngens(R);
	msg := Sprintf("Runtime error in '.': Value for name index (%o) should be in the range [1..%o]", i, n);
	error msg;
    end if;

    return Generators(R)[i];
end intrinsic;

intrinsic ResolutionCycles(R::ChowRngHMS) -> SeqEnum
{Return an AssociativeArray whose keys are (representatives of) the singular points of the
Bailey Borel compactification of the Hilbert Modular surface associated to `R`, and the value
at `p` is a sequence listing the generators of `R` corresponding to the resolution cycles over
the point `p`}
    A := R`ResolutionCycles;
    B := AssociativeArray();
    gens := Generators(R);

    for p in Keys(A) do
	B[p] := [gens[i] : i in A[p]];
    end for;
    return B;
end intrinsic;

intrinsic ResolutionCycleIndices(R::ChowRngHMS) -> SeqEnum
{Return an AssociativeArray whose keys are (representatives of) the singular points of the
Bailey Borel compactification of the Hilbert Modular surface associated to `R`, and the value
at `p` is a sequence listing the indices of the generators of `R` corresponding to the
resolution cycles over the point `p`}
    return R`ResolutionCycles;
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

intrinsic Ngens(R::ChowRngHMS) -> RngIntElt
{}
    return #Generators(R);
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
    return IntersectionRing(CongruenceSubgroup(R), BR);
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

intrinsic BaseRing(y::ChowRngHMSElt) -> Rng
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

    return CreateElement(R, newcom);
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
    if not boo then return false, _; end if;

    R := Parent(x);
    z := u * x - One(R);
    return true, u*(One(R) - z + z^2);
end intrinsic;


intrinsic IsCoercible(X::ChowRngHMS, y::Any) -> BoolElt, .
{Return whether y is coercible into X and the result if so}

    if Type(y) eq RngIntElt then
	return true, CreateElement(X, 1, 0, 0);
    end if;

    if Type(y) eq ChowRngHMSElt and Parent(y) eq X then
	return true, y;
    end if;

    return false, "Illegal coercion.";
end intrinsic;

intrinsic GeneratorInfo(x::ChowRngHMSElt) -> Any
{Given a generator, return either "Canonical", or the singular point on the Hilbert modular
surface associated to `x`.}
    R := Parent(x);
    try
	return R`GeneratorInfo[x];
    catch e
	error "Element not recognized as a generator for ", R;
    end try;
end intrinsic;


/////////////////////////////////////////////////////
//
//    Creation
//
/////////////////////////////////////////////////////

// TODO? Depending on the subgroup, there may be MANY different quotient singularities
//       and cusps to resolve. It may be a good idea to implement a "Diagonal" option
//       to compress all the singularities of the same type into a single intersection class.
//
intrinsic IntersectionRing(Gamma::GrpHilbert, BR::Rng) -> ChowRngHMS
{Computes the Chow ring of the minimal desingularization of the Bailey-Borel compactification
of the Hilbert Modular Surface with coefficients in BR.}

    R := New(ChowRngHMS);
    R`CongruenceSubgroup := Gamma;
    R`GeneratorInfo := AssociativeArray();
    R`ResolutionCycles := AssociativeArray();
    R`GeneratorInfo := AssociativeArray();

    // The method to compute the Chow Ring of a Hilbert Modular Surface is based on
    // van der Geer's "Hilbert Modular Surfaces" (referred to as [vdG]). The first result
    // we need is
    //
    // Theorem [vdG, p121]: The cohomology of a Hilbert Modular Surface is generated by
    // The classes of the Chern forms and the resolution cycles.
    //
    // Thus, the majority of the work is to determine the interesction structure of the
    // resolution cycles. Much of this is described in [vdG, Chapters II-IV].
    //
    // Once the local resolution cycles have been determined, we can compute the intersection
    // numbers of the first Chern class with the local Chern cycles. A formula for c1(X)^2
    // is given in [vdg, Theorem IV.2.5].


    // Figure out the number of elliptic + parabolic points and the lengths of the
    // resolution cycles.

    //////////////
    // Elliptic Points

    EPData := EllipticPointData(Gamma);
    rawEllipticResolutionData := [];

    shift := 2;
    for singType in Keys(EPData) do

	//localChernCoeffs := QuotientLocalChernCoefficients(singType, head cat tail);
	selfINumbers, localChernCoeffs := EllipticLocalChernData(singType);

	for i in [1..EPData[singType]] do
	    Append(~rawEllipticResolutionData, <selfINumbers, localChernCoeffs>);

	    // Associate a singular point to the resolution cycle.
	    P := SingularPointHMS("Elliptic", singType);

	    // Populate the Resolution Cycle dictionary with indices.
	    numCycles := #localChernCoeffs;
	    R`ResolutionCycles[P] := [(shift - 1) + 1 .. (shift - 1) + numCycles];

	    // Update shift.
	    shift +:= numCycles;
	end for;

    end for;

    //////////////
    // Parabolic Points

    cusps := Cusps(Gamma);
    rawParabolicResolutionData := [];
    for c in cusps do
		minimalSequence, nb := CuspResolutionIntersections(Gamma, c[3]);
        positiveSelfIntersectionNumbers := [-x : x in RepeatSequence(minimalSequence, nb)];
        localChernCoeffs := [1 : i in [1..#positiveSelfIntersectionNumbers]];
        Append(~rawParabolicResolutionData, <positiveSelfIntersectionNumbers, localChernCoeffs>);
    end for;

    for par in rawParabolicResolutionData do
	P := SingularPointHMS("Cuspidal", <"Fake">);
	R`ResolutionCycles[P] := [(shift - 1) + 1 .. (shift - 1) + #par[2]];
	shift +:= #par[2];
    end for;

    //////////////
    // Assembly of main structures.

    //////////////////////
    // Set up the multiplication table.

    // The multiplication table is determined by the resolution cycles.

    M := _RawToIntersectionMatrix(Gamma, BR, rawEllipticResolutionData, rawParabolicResolutionData);
    R`MultiplicationTable := M;
    D := Nrows(M)-2;

    //////////////////////
    // Set up the graded components.

    R0 := RSpace(BR, 1);
    R1 := RSpace(BR, D);
    R2 := RSpace(BR, 1);
    R`GradedComponents := <R0, R1, R2>;

    // Finally, Cache the generators, since I suspect users will use them often.
    R`Generators := [CreateElement(R, 0, R1.i, 0) : i in [1..D]];

    // Update the resolution cycle dictionary with a new singular point, and

    for P in Keys(R`ResolutionCycles) do
	for i in R`ResolutionCycles[P] do
	    R`GeneratorInfo[R.i] := P;
	end for;
    end for;

    R`GeneratorInfo[R.1] := "Canonical";

    return R;
end intrinsic;


///////// Hilferfunktionen ///////////

intrinsic _RawToIntersectionMatrix(G::GrpHilbert, BR::Rng, ellipticData, parabolicData) -> MtrxSprs
{}

    if #ellipticData gt 0 then
	ned := &+[#resolutionTuple[1] : resolutionTuple in ellipticData];
    else
	ned := 0;
    end if;

    if #parabolicData gt 0 then
	npd := &+[#resolutionTuple[1] : resolutionTuple in parabolicData];
    else
	npd := 0;
    end if;

    D := 1 + ned + npd;

    // NOTE: We "store" multiplication values for the cross-degree terms.
    M := SparseMatrix(BR, D+2, D+2);

    // We compute this by updating it with the local Chern class information.
    // It is eventually an integer, but only after all of the updates.
    firstChernNumber := 2 * VolumeOfFundamentalDomain(G);

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
	// NOTE: The resolution cycle for a cyclic quotient singularity is a chain of
	//       P1's.
	resolutionCycle := resolutionData[1];
	chernCoeffs := resolutionData[2];

	for i in [1..#resolutionCycle-1] do
	    M[shift+i, shift+i] := -resolutionCycle[i];
	    M[shift+i, shift+i+1] := 1;
	    M[shift+i+1, shift+i] := 1;
	end for;

	// Update the last row/column in the block.
	i := #resolutionCycle;
	M[shift + i, shift + i] := -resolutionCycle[i];

	// Update the coefficients of the first Chern cycle using the local Chern
	// cycle data.
	//
	// NOTE: These local Chern coefficients are often rational numbers!

	for i in [1..#resolutionCycle] do

	    nrc := #resolutionCycle;
	    // NOTE: Canonical is -c1(TX). Thus, we reverse our sign here.
	    kappa_dot_localChern := &+[chernCoeffs[j] * M[shift+i, shift+j] : j in [1..nrc]];
	    M[2, shift+i] := kappa_dot_localChern;
	    M[shift+i, 2] := kappa_dot_localChern;
	end for;

	// Finally, we need the update to c1^2 from the local Chern cycle.
	for i in [1..#resolutionCycle] do
	    for j in [1..#resolutionCycle] do
		firstChernNumber +:= chernCoeffs[i] * M[shift+i, shift+j] * chernCoeffs[j];
	    end for;
	end for;

	// Update the shift.
	shift +:= #resolutionCycle;
    end for;

    /////////////////////
    // Populate parabolic resolution data.
    for resolutionData in parabolicData do

	// NOTE: For a cuspidal resolution, the Chern coefficients are all equal to 1.
	resolutionCycle  := resolutionData[1];
	chernCoeffs := resolutionData[2];

	for i in [1..#resolutionCycle-1] do
	    M[shift+i, shift+i] := -resolutionCycle[i];
	    M[shift+i, shift+i+1] := 1;
	    M[shift+i+1, shift+i] := 1;
	end for;

	// Update the last row/column in the block.
	i := #resolutionCycle;
	M[shift + i, shift + i] := -resolutionCycle[i];

	if i gt 1 then
	    M[shift + 1, shift + i] := 1;
	    M[shift + i, shift + 1] := 1;
	end if;

	// Update the coefficients of the first Chern cycle using the local Chern
	// cycle data.
	// NOTE: Canonical is -c1(TX). Thus, we reverse our sign here.

        // Correction term when there is a single resolution cycle.
        correctionTerm := i eq 1 select 2 else 0;

	for i in [1..#resolutionCycle] do
            localTerm := resolutionCycle[i] - 2 + correctionTerm;
	    M[2, shift+i] := localTerm;
	    M[shift+i, 2] := localTerm;

            // UpdlocalTermte first Chern Number with loclocalTerml term
            firstChernNumber +:= -localTerm;
	end for;

	// Update the shift.
	shift +:= #resolutionCycle;
    end for;

    // The very last thing to do is update the canonical class.
    M[2,2] := firstChernNumber;
    return M;
end intrinsic;


intrinsic EllipticLocalChernData(type::Tup : PrintCs:=false) -> SeqEnum, SeqEnum
{Return the self intersection numbers of the resolution cycles over an elliptic point, as
well as the (possibly rational) coefficients of the local Chern cycle of a quotient singularity.}

    // NOTE: Figuring out the local Chern cycle is a little tricky, as it is actually
    //       a QQ-divisor! See [vdG, p. 64]. For the definition of the (li, mi), see
    //       [vdG, p. 53].

    // In order to compute the local Chern cycle, we need the coordinates of the points
    // on the lower convex hull associated to the (positive) exponents.

    // Massage the type so that <a,b> = <1, positive>
    stdForm := <type[1], 1, (type[3] + (1 - type[2])) mod type[1]>;

    n := type[1];
    assert type[2] eq 1;
    q := type[3] mod n;

    _, _, qpr := XGCD(n, q);
    qpr := qpr mod n;
    assert (qpr*q) mod n eq 1;

    // Compute the HJContinuedFraction of n/qpr. See [p.43, vdG].
    selfIntersectionNumbers := HJContinuedFraction(stdForm[1]/qpr);

    RM := VectorSpace(Rationals(), 2);
    C0 := RM ! [1,0];
    C1 := RM ! [qpr/n, 1/n];

    c := [0] cat selfIntersectionNumbers;
    C := [C0, C1] cat [Zero(RM) : i in [2..#c-2]];

    // Choose `d` as in [vdG]. That is, the length of the continued fraction
    // expansion (plus one).
    d := #selfIntersectionNumbers;

    // Use the equation C[i] * ci = C[i+1] + C[i-1]. Note the indices are off
    // by one from [vdG].
    for i in [1..d] do
	C[i+2] := c[i+1] * C[i+1] - C[i];
    end for;

    // Now that we have the coordinates, we can return the list of  (li + mi - 1).
    // Note that the beginning and ending terms of the `C` don't correspond to curves
    // in the resolution cycle, but instead to "coordinate axes" of `G\CC^2`. These points
    // are necessarily equal to `(1,0)` and `(0,1)`, so cancel

    lst := [c[1] + c[2] - 1 : c in C];
    assert lst[1] eq 0 and lst[#lst] eq 0;
    assert #lst ge 3; //i.e., check the resolution cycle has at least one curve.

    if PrintCs then
	print C;
    end if;

    return selfIntersectionNumbers, lst[2..#lst-1];
end intrinsic;

/////////////////////////////////////////////////////
//
//    Creation Dispatch
//
/////////////////////////////////////////////////////

intrinsic IntersectionRing(Gamma::GrpHilbert) -> ChowRngHMS
{Equivalent to IntersectionRing(Gamma, Integers()).}
    return IntersectionRing(Gamma, Integers());
end intrinsic;

intrinsic IntersectionRing(F::FldNum) -> ChowRngHMS
{Computes the Chow ring of the Bailey-Borel compactification of the Hilbert Modular Surface.}
        return IntersectionRing(F, 1*RingOfIntegers(F));
end intrinsic;

intrinsic IntersectionRingOfCuspidalResolution(F::FldNum) -> ChowRngHMS
{Computes the Chow ring of the surface resolving the cusp singularities of the Hilbert Modular Surface.}
    return IntersectionRingOfCuspidalResolution(F, 1*RingOfIntegers(F));
end intrinsic;

intrinsic IntersectionRingOfMinimalResolution(F::FldNum) -> ChowRngHMS
{Computes the Chow ring of the minimal resolution of the singularities of the Hilbert Modular Surface.}
    return IntersectionRingOfMinimalResolution(F, 1*RingOfIntegers(F));
end intrinsic;

intrinsic IntersectionRing(M::ModFrmHilDGRng, N::RngOrdIdl) -> ChowRngHMS
{Computes the Chow ring of the Bailey-Borel compactification of the Hilbert Modular Surface.}
    error "Not Implemented.";
end intrinsic;

intrinsic IntersectionRingOfCuspidalResolution(M::ModFrmHilDGRng, N::RngOrdIdl) -> ChowRngHMS
{Computes the Chow ring of the surface resolving the cusp singularities of the Hilbert Modular Surface.}
    error "Not Implemented.";
end intrinsic;

intrinsic IntersectionRingOfMinimalResolution(M::ModFrmHilDGRng, N::RngOrdIdl) -> ChowRngHMS
{Computes the Chow ring of the minimal resolution of the singularities of the Hilbert Modular Surface.}
    error "Not Implemented.";
end intrinsic;

intrinsic IntersectionRing(F::FldNum, N::RngOrdIdl) -> ChowRngHMS
{Computes the Chow ring of the Bailey-Borel compactification of the Hilbert Modular Surface.}
    Gamma := CongruenceSubgroup(F, N);
    return IntersectionRing(Gamma);
end intrinsic;

intrinsic IntersectionRingOfCuspidalResolution(F::FldNum, N::RngOrdIdl) -> ChowRngHMS
{Computes the Chow ring of the surface resolving the cusp singularities of the Hilbert Modular Surface.}
    Gamma := CongruenceSubgroup(F, N);
    return IntersectionRingOfCuspidalResolution(Gamma);
end intrinsic;

intrinsic IntersectionRingOfMinimalResolution(F::FldNum, N::RngOrdIdl) -> ChowRngHMS
{Computes the Chow ring of the minimal resolution of the singularities of the Hilbert Modular Surface.}
    Gamma := CongruenceSubgroup(F, N);
    return IntersectionRingOfMinimalResolution(Gamma);
end intrinsic;

intrinsic IntersectionRingOfCuspidalResolution(Gamma::GrpHilbert) -> ChowRngHMS
{Computes the Chow ring of the surface resolving the cusp singularities of the Hilbert Modular Surface.}
    error "Not Implemented.";
end intrinsic;

intrinsic IntersectionRingOfMinimalResolution(Gamma::GrpHilbert) -> ChowRngHMS
{Computes the Chow ring of the minimal resolution of the singularities of the Hilbert Modular Surface.}
    error "Not Implemented.";
end intrinsic;


/////////////////////////////////////////////////////
//
//    Greater functionality
//
/////////////////////////////////////////////////////

intrinsic IntersectionMatrix(R::ChowRngHMS) -> MtrxSprs
{Return the matrix [R.i * R.j : i,j] of cycles of degree 1 in the Hilbert Modular Surface.}
    M := MultiplicationTable(R);
    n := Ncols(M);
    return Submatrix(M, [2..n-1], [2..n-1]);
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




intrinsic ChernNumber(F::FldNum, level::RngOrdIdl) -> RngIntElt
{Returns the ith Chern number of the
minimal resolution of the Hilbert Modular Surface for the Hilbert Modular Group.}
    return ChernNumbersOfMinimalResolution(F, level);
end intrinsic;


intrinsic ArithmeticGenus(F::FldNum, level::RngOrdIdl) -> RngIntElt
{returns chi the arithmetic genus}
    c12, c2 := ChernNumbersOfMinimalResolution(F, level);
    return (c12 + c2)/12;
end intrinsic;

intrinsic ArithmeticGenus(F::FldNum) -> RngIntElt
{returns chi the arithmetic genus}
    return ArithmeticGenus(F, 1*Integers(F));
end intrinsic;

intrinsic VolumeOfFundamentalDomain(F::FldNum) -> FldRatElt
{Return the Volume of the fundamendal domain of the (non-compact) Hilbert Modular Surface.}
    return VolumeOfFundamentalDomain(F, 1*MaximalOrder(F));
end intrinsic;

/////////////////////////////////////////////////////
//
//    Dispatch for Number Field Input plus level.
//
/////////////////////////////////////////////////////

intrinsic ChernNumbersOfMinimalResolution(F::FldNum, N::RngOrdIdl) -> SeqEnum
{Returns a tuple <c1^2, c2> corresponding to the Chern numbers of the
minimal resolution of the Hilbert Modular Surface for the Hilbert Modular Group.}
    Gamma := CongruenceSubgroup(F, N);
    return ChernNumbersOfMinimalResolution(Gamma);
end intrinsic;

intrinsic VolumeOfFundamentalDomain(F::FldNum, N::RngOrdIdl) -> FldRatElt
{Return the Volume of the fundamendal domain of the (non-compact) Hilbert Modular Surface.}
    Gamma := CongruenceSubgroup(F, N);
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
    Gamma := CongruenceSubgroup(BaseField(M), N);
    return ChernNumbersOfMinimalResolution(Gamma);
end intrinsic;


intrinsic VolumeOfFundamentalDomain(M::ModFrmHilDGRng, N::RngOrdIdl) -> ChowRngHMS
{Return the Volume of the fundamendal domain of the (non-compact) Hilbert Modular Surface.}
    Gamma := CongruenceSubgroup(BaseField(M), N);
    return VolumeOfFundamentalDomain(Gamma);
end intrinsic;


/////////////////////////////////////////////////////
//
//    General Hilbert Modular Surface code.
//
/////////////////////////////////////////////////////

intrinsic ChernNumbersOfMinimalResolution(Gamma::GrpHilbert) -> SeqEnum
{Returns `c1^2, c2`,  corresponding to the Chern numbers of the
minimal resolution of the Hilbert Modular Surface for the Hilbert Modular Group.}
    return ChernNumbers(IntersectionRing(Gamma));
end intrinsic;


intrinsic ChernNumbers(R::ChowRngHMS) -> RngIntElt, RngIntElt
{Return the Chern numbers `c1^2, c2` of the Hilbert Modular Surface associated to `R`.}

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

  //// Computing c1^2.
  firstChernNumber := MultiplicationTable(R)[2,2];

  //// Computing the Euler number (c2)
  // 1. Determine the Volume of Gamma.
  volume := VolumeOfFundamentalDomain(CongruenceSubgroup(R));

  // 2. Count resolution cycles.
  Rcs := ResolutionCycleIndices(R);
  singularities := Keys(Rcs);

  secondChernNumber := volume;

  for p in singularities do
      if p`SingularityType eq "Quotient" then
	  tup := p`SingularityInfo;
	  n := tup[1];
	  secondChernNumber +:= #Rcs[p] + (n-1)/n;

      elif p`SingularityType eq "Cusp" then
	  secondChernNumber +:= #Rcs[p];

      else
	  error "Singular point has unexpected value in `SingularityType`:", p`SingularityType;
      end if;
  end for;

  // For a nonsingular surface, this must be an integer.
  secondChernNumber := Integers() ! secondChernNumber;

  return firstChernNumber, secondChernNumber;
end intrinsic;

intrinsic ChernNumber(R::ChowRngHMS, i::RngIntElt) -> RngIntElt
{Return the `i`-th Chern number of the Hilbert Modular Surface associated to `R`.}
    c1sqed, c2 := ChernNumbers(R);
    return [c1sqed, c2][i];
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


intrinsic VolumeOfFundamentalDomain(Gamma::GrpHilbert) -> FldRatElt
{Return the Volume of the fundamendal domain of the (non-compact) Hilbert Modular Surface.}
    return 2 * Index(Gamma) * DedekindZetaExact(BaseField(Gamma), -1);
end intrinsic;

intrinsic ChernNumbersOfLogCanonical(Gamma::GrpHilbert) -> FldRatElt, FldRatElt
{Return the Chern numbers of the log-canonical sheaf.}
    vol := VolumeOfFundamentalDomain(Gamma);
    return 2 * vol, vol;
end intrinsic;

intrinsic ChernNumberOfLogCanonical(Gamma::GrpHilbert, i::RngIntElt) -> FldRatElt
{Return the i-th Chern number of the log-canonical sheaf.}
    a, b := ChernNumbersOfLogCanonical(Gamma);
    return [a, b][i];
end intrinsic;

intrinsic ChernNumbersOfLogCanonical(R::ChowRngHMS) -> FldRatElt
{Return the Chern numbers of the log-canonical class.}
    return ChernNumbersOfLogCanonical(CongruenceSubgroup(R));
end intrinsic;

intrinsic ChernNumberOfLogCanonical(R::ChowRngHMS, i::RngIntElt) -> FldRatElt
{Return the i-th Chern number of the log-canonical class.}
    return ChernNumberOfLogCanonical(CongruenceSubgroup(R), i);
end intrinsic;


intrinsic Covolume(Gamma::GrpHilbert) -> FldRatElt
{Alias for VolumeOfFundamentalDomain.}
    return VolumeOfFundamentalDomain(Gamma);
end intrinsic;


intrinsic LocalChernCycle(R::ChowRngHMS, P::StupidSingularPointHMS) -> ChowRngHMSElt
{Given a singular point on a Hilbert Modular Surface, return the local Chern cycle of
resolution curves over `P`. If the coefficients of the local Chern cycle are coercible
into the base ring of `R`, then the result is returned as an element of `R`. Otherwise,
an error is thrown.}

    indices := ResolutionCycleIndices(R)[P];
    cycles  := ResolutionCycles(R)[P];

    if P`SingularityType eq "Cusp" then
	return &+cycles;
    end if;

    // Otherwise, P must be a quotient singularity.
    assert P`SingularityType eq "Quotient";
    _, coeffs := EllipticLocalChernData(P`SingularityInfo);

    if &and [IsCoercible(BaseRing(R), y) : y in coeffs] then
	return &+[coeffs[i] * cycles[i] : i in [1..#cycles]];
    end if;
    error "(Rational) Coefficients of local Chern cycle not coercible into Chow ring.";
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////
//
// Alias
//
/////////////////////////////////////////////////////////////////////////////////

intrinsic ChowRing(Gamma::GrpHilbert) -> ChowRngHMS
{}
    return IntersectionRing(Gamma);
end intrinsic;

intrinsic ChowRing(Gamma::GrpHilbert, BR::Rng) -> ChowRngHMS
{}
    return IntersectionRing(Gamma, BR);
end intrinsic;


/////////////////////////////////////////////////////////////////////////////////
//
// Conversion
//
/////////////////////////////////////////////////////////////////////////////////

intrinsic AffineAlgebra(R::ChowRngHMS) -> RngMPolRes, UserProgram
{Return a ring `R[x1, ..., xn]/I` isomorphic to `R`, and a conversion function.}

    D  := #Generators(R) + 1;
    PR := PolynomialRing(BaseRing(R), D);
    T  := MultiplicationTable(R);
    PRtop := PR.D;

    relations := [PR.i * PR.j - T[i,j] * PRtop : i, j in [1..D]];
    I := ideal<PR | relations>;

    // Construct the conversion function.
    function foo(x)
	coeffs := Coefficients(x);

	return coeffs[1] + &+[coeffs[i+1] * PR.i : i in [1..D]];
    end function;

    return quo<PR | I>, foo;
end intrinsic;


intrinsic RegularRepresentation(R::ChowRngHMS) -> AlgMat, UserProgram
{Return a matrix algebra corresponding to the regular representation of R.}

    BR := BaseRing(R);
    B := Basis(R);

    mats := [Matrix(BR, [Coefficients(a * b) : a in B]) : b in B];
    AR := MatrixAlgebra<BR, #B | mats>;

    // Construct the conversion function.
    function foo(x)
	coeffs := Coefficients(x);
	return &+[coeffs[i] * AR.i : i in [1..#B]];
    end function;

    return AR, foo;
end intrinsic;
