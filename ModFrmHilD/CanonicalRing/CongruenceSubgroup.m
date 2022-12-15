
/////////////////////////////////////////////////////
//
//    Type Hook
//
/////////////////////////////////////////////////////

// This is a dummy type so that when general congruence
// subgroups are implemented, the functionality can be
// hooked in easily.

declare type GLPlus_Type;
declare type SL_Type;

declare type GAMMA_Type;
declare type GAMMA_0_Type;
declare type GAMMA_1_Type; // Gamma types

declare type GrpHilbert;
declare attributes GrpHilbert : Field,
        AmbientType,
	PrintString,
	Level,
	Index,
	EllipticPointData,
	ComponentIdeal,
	GammaType;

/////////////////// Creation ///////////////////

intrinsic IsRealQuadraticField(F::FldNum) -> BoolElt
{}
    return Degree(F) eq 2 and BaseRing(F) eq Rationals() and Discriminant(F) gt 0;
end intrinsic;

// Main constructor from which all else is derivedn
intrinsic CongruenceSubgroup(Gtype, F::FldNum, N::RngOrdIdl, B::RngOrdIdl)
          -> StupidCongruenceSubgroup
{Create a dummy type. This is a placeholder for a future CongruenceSubgroup type.
The B refers to the component, i.e., whether it is a subgroup of Gamma(O_F + B). }
    
    require IsRealQuadraticField(F): "Number field must be Real Quadratic Field.";
    Gamma := New(StupidCongruenceSubgroup);
    Gamma`Field := F;
    Gamma`ComponentIdeal := B;
    Gamma`Level := N;
    Gamma`Index := IndexOfPrincipalCongruenceSubgroup(F, N);
    Gamma`GammaType := GAMMA_Type;

    case Gtype:
    when "SL": Gamma`AmbientType := SL_Type;
    when "GL+": Gamma`AmbientType := GLPlus_Type;
    else
        error "Ambient type not supported.";
    end case;
    
    return Gamma;
end intrinsic;


intrinsic CongruenceSubgroup(F::FldNum) -> GrpHilbert
{Create a dummy type. This is a placeholder for a future CongruenceSubgroup type.}
    return CongruenceSubgroup(F, 1*MaximalOrder(F));
end intrinsic;

intrinsic CongruenceSubgroup(F::FldNum, N::RngOrdIdl) -> GrpHilbert
{Create a dummy type. This is a placeholder for a future CongruenceSubgroup type.}
    return CongruenceSubgroup(F, N, 1*MaximalOrder(F));
end intrinsic;

intrinsic CongruenceSubgroup(F::FldNum, N::RngQuad) -> GrpHilbert
{}
    if N eq 1*MaximalOrder(F) then
	return CongruenceSubgroup(F);
    else
	error "CongruenceSubgroup not implemented for arbitrary orders.";
    end if;
end intrinsic;

intrinsic CongruenceSubgroup(F::FldNum, N::RngOrdIdl, B::RngOrdIdl) -> GrpHilbert
{}
    return CongruenceSubgroup("SL", F, N, B);
end intrinsic;
                                                                       
intrinsic CongruenceSubgroup(F::FldNum, N::RngOrdIdl, B::RngOrdIdl) -> GrpHilbert
{Create a dummy type. This is a placeholder for a future CongruenceSubgroup type.
The B refers to the component, i.e., whether it is a subgroup of Gamma(O_F + B). }

    require IsRealQuadraticField(F): "Number field must be Real Quadratic Field.";

    Gamma := New(GrpHilbert);
    Gamma`Field := F;
    Gamma`ComponentIdeal := B;
    Gamma`Level := N;
    Gamma`Index := IndexOfPrincipalCongruenceSubgroup(F, N);
    Gamma`GammaType := "Gamma";
    return Gamma;
end intrinsic;

// At the moment, this is the only way to create a group of type Gamma_0(N).
intrinsic Gamma0(F::FldNum) -> GrpHilbert
{Return the Hilbert Modular group over `F`.}
    return Gamma0(F, 1*MaximalOrder(F));
end intrinsic;


intrinsic Gamma0(F::FldNum, N::RngOrdIdl) -> GrpHilbert
{Return the Congruence Subgroup Gamma_0(N) over the number field `F`.}
    return Gamma0(F, N, 1*MaximalOrder(F));
end intrinsic;

intrinsic Gamma0(F::FldNum, N::RngOrdIdl, B::RngOrdIdl) -> StupidCongruenceSubgroup
{}
    return Gamma0("SL", F, N, B);
end intrinsic;

intrinsic Gamma0(G, F::FldNum, N::RngOrdIdl, B::RngOrdIdl) -> StupidCongruenceSubgroup
{Return the Congruence Subgroup Gamma_0(N) over the number field `F`.}
    G := CongruenceSubgroup(F, N, B);
    if N ne 1*MaximalOrder(F) then
	// Reassign all the important information.
	G`GammaType := GAMMA_0_Type;
	G`Index := IndexOfGamma0(F, N);
    end if;
    return G;
end intrinsic;


intrinsic Gamma1(F::FldNum) -> StupidCongruenceSubgroup
{Return the Hilbert Modular group over `F`.}
    return Gamma1(F, 1*MaximalOrder(F));
end intrinsic;

intrinsic Gamma1(F::FldNum, N::RngOrdIdl) -> StupidCongruenceSubgroup
{Return the Congruence Subgroup Gamma_1(N) over the number field `F`.}
    return Gamma1(F, N, 1*MaximalOrder(F));
end intrinsic;

intrinsic Gamma1(F::FldNum, N::RngOrdIdl, B::RngOrdIdl) -> StupidCongruenceSubgroup
{}
    return Gamma1("SL", F, N, B);
end intrinsic;
                                                               
intrinsic Gamma1(G, F::FldNum, N::RngOrdIdl, B::RngOrdIdl) -> StupidCongruenceSubgroup
{Return the Congruence Subgroup Gamma_0(N) over the number field `F`.}
    G := CongruenceSubgroup(F, N, B);
    if N ne 1*MaximalOrder(F) then
	// Reassign all the important information.
	G`GammaType := GAMMA_1_Type;
	G`Index := IndexOfGamma1(F, N);
    end if;
    return G;
end intrinsic;


/////////////////// Printing ///////////////////

intrinsic Print(Gamma::GrpHilbert)
{Print.}
    print "Congruence Subgroup of Hilbert Modular group.";
    print "Field:", Field(Gamma);
    printf "Level: (%o)\n", IdealOneLine(Level(Gamma));
    printf "Component: (%o)\n", IdealOneLine(Component(Gamma));
    print "Index: ", Index(Gamma);
    print "Gamma Type:", GammaType(Gamma);
    print "Supergroup:", GammaType(Gamma);
    return;
end intrinsic;


////////// GrpHilbert access to attributes //////////

intrinsic Level(Gamma::GrpHilbert) -> RngOrdIdl
{Return the Level attribute}
    return Gamma`Level;
end intrinsic;

intrinsic Field(Gamma::GrpHilbert) -> FldNum
{Return the Level attribute}
    return Gamma`Field;
end intrinsic;

intrinsic Index(Gamma::GrpHilbert) -> RngIntElt
{Return the Index Attribute.}
    return Gamma`Index;
end intrinsic;

intrinsic ComponentIdeal(Gamma::GrpHilbert) -> RngOrdIdl
{Return the ComponentIdeal Attribute. That is, \frak(b), the ideal indexing the
component of the Hilbert Modular Surface}
    return Gamma`ComponentIdeal;
end intrinsic;

intrinsic Component(Gamma::GrpHilbert) -> RngIntElt
{Return the ComponentIdeal Attribute. That is, \frak(b), the ideal indexing the
component of the Hilbert Modular Surface}
    return ComponentIdeal(Gamma);
end intrinsic;

intrinsic GammaType(Gamma::GrpHilbert) -> Any
{}
    return Gamma`GammaType;
end intrinsic;

intrinsic AmbientType(Gamma::GrpHilbert) -> Any
{}
    return Gamma`AmbientType;
end intrinsic;


////////// Basic functionality //////////

intrinsic 'eq'(Gamma1::GrpHilbert, Gamma2::GrpHilbert) -> BoolElt
{}
    return (Field(Gamma1) eq Field(Gamma2) and
	    Level(Gamma1) eq Level(Gamma2) and
	    Index(Gamma1) eq Index(Gamma2));
end intrinsic;


/////////////////////////////////////////////////////////////////////////////////
//
// Elliptic points (i.e., quotient singularities)
//
/////////////////////////////////////////////////////////////////////////////////

intrinsic EllipticPointData(Gamma::GrpHilbert) -> Assoc
{Given a congruence subgroup, return an associative array  A := (<r, a, b> => RngIntElt).
The keys of this associative array are tuples <r; a, b> describing the local type of
the elliptic point. By this, we mean an elliptic point with a stabilizer locally generated
by

(zeta_r^a, zeta_r^b)

where zeta_r is a primitive r-th root of unity. The quantity A[<r, a, b>] is the number of
elliptic points of this type up to congugacy in Gamma.
}

    if assigned Gamma`EllipticPointData then return Gamma`EllipticPointData; end if;

    // This method relies on the tables of van der Geer for the most part. Given a level "N",
    // we first rely on the comment in [vdG, p. 109].

    // Proposition: If Gamma is the principal congruence subgroup of level N of the Hilbert
    //              modular group Gamma_{K, \frak{b}}, and N^2 is not equal to either (2) or (3),
    //              then Gamma acts freely on the squared upper half plane.

    // Thus, the first thing is the level and return an empty array in the trivial cases.

    K := Field(Gamma);
    ZK := RingOfIntegers(K);
    D := Discriminant(K);
    N := Level(Gamma);
    B := ComponentIdeal(Gamma);

    // Ensure that B and the level are coprime before doing any computations.
    q := CoprimeNarrowRepresentative(B, 6*N);
    B := Integers() ! (Norm(q) * Norm(B));

    ellipticData := AssociativeArray();
    if IsPrincipalCongruenceSubgroup(Gamma) and N^2 notin [1*ZK, 2*ZK, 3*ZK] then
	return ellipticData;
    end if;

    // TODO: XXX: Properly implement elliptic points for arbitrary congruence subgroups.
    if not IsPrincipalCongruenceSubgroup(Gamma) then
	error "Not implemented for non-principal congruence subgroups.";
    end if;

    // The next thing to check is if we are in one of the special discriminant cases.
    // The special discriminants vis a vis torsion are D = 5, 8, 12.
    if D in [5,8,12] then
	return _EllipticPointDataSpecialCases(Gamma);
    end if;

    if Index(Gamma) eq 1 then
	// If we are looking at the full Hilbert Modular Group with component \frak{b},
	// then [vdG, p. 267] provides tables to compute the number and types of torsion points.

	// Order 2 points.
	//
	if D mod 4 eq 1 then
	    ellipticData[<2,1,1>] := ClassNumber(-4*D);
	elif D mod 8 eq 0 then
	    ellipticData[<2,1,1>] := 3*ClassNumber(-D);
	else
	    Dby4 := ExactQuotient(D, 4);
	    h := ClassNumber(-Dby4);

	    case [Dby4 mod 8, B mod 4]:
	    when [3,1]:
		ellipticData[<2,1,1>] := 10*h;
	    when [3,3]:
		ellipticData[<2,1,1>] := 10*h;
	    when [7,1]:
		ellipticData[<2,1,1>] := 4*h;
	    when [7,3]:
		ellipticData[<2,1,1>] := 4*h;
	    end case;
	end if;

	// Order 3 points
	//
	if D mod 3 ne 0 then
	    h := ExactQuotient(ClassNumber(-3*D), 2);
	    ellipticData[<3,1, 1>] := h;
	    ellipticData[<3,1,-1>] := h;
	else
	    Dby3 := ExactQuotient(D, 3);
	    h := ClassNumber(-Dby3);

	    case [Dby3 mod 3, B mod 3]:
	    when [1,1]:
		ellipticData[<3,1,1>] := 4*h;
		ellipticData[<3,1,-1>] := h;

	    when [1,2]:
		ellipticData[<3,1,1>] := h;
		ellipticData[<3,1,-1>] := 4*h;

	    when [2,1]:
		ellipticData[<3,1,1>] := 3*h;
		ellipticData[<3,1,-1>] := 0;

	    when [2,2]:
		ellipticData[<3,1,1>] := 0;
		ellipticData[<3,1,-1>] := 3*h;
	    end case;
	end if;

    elif IsPrincipalCongruenceSubgroup(Gamma) then
	// Let A := Norm(\frak{b}), where \frak{b} := ComponentIdeal(Gamma). We use the following
	// remark of [vdG, p. 110]
	//
	// Proposition: If (A, N) = 1, then the number of elliptic points is given by...
	//
	if N^2 eq 2*ZK then
	    if D mod 8 eq 0 then
		ellipticData[<2, 1, 1>] := 6 * ClassNumber(-D);
	    elif D mod 4 eq 0 then
		Dby4 := ExactQuotient(D, 4);
		h := ClassNumber(-Dby4);

		case Dby4 mod 8:
		when 7:
		    ellipticData[<2, 1, 1>] := 12 * h;

		when 3:
		     ellipticData[<2, 1, 1>] := 24 * h;
		end case;
	    end if;

	elif N^2 eq 3*ZK then
	    if D mod 3 eq 0 then
		Dby3 := ExactQuotient(D, 3);
		h := ClassNumber(-Dby3);

		// In each case, there are no points of the other type.
		case (B*D) mod 9:
		when 6:
		    ellipticData[<3, 1, 1>] := 12 * h;

		when 3:
		    ellipticData[<3, 1, -1>] := 12 * h;
		end case;
	    end if;
	end if;
	//
	// (End of Theorem)
    end if;

    // Assign into Gamma and return
    Gamma`EllipticPointData := ellipticData;
    return ellipticData;
end intrinsic;

intrinsic _EllipticPointDataSpecialCases(Gamma::GrpHilbert) -> Assoc
{Deal with the specific cases of discriminant 5, 8, 12.}

    D := Discriminant(Field(Gamma));
    ellipticData := AssociativeArray();
    require Index(Gamma) eq 1 : "Only implemented for level 1 for special discrminants.";

    if D eq 5 then
	ellipticData[<2, 1, 1>] := 2;
	ellipticData[<3, 1, 1>] := 1;
	ellipticData[<3, 1,-1>] := 1;
	ellipticData[<5, 1, 3>] := 1; // Type <5, 2, 1>
	ellipticData[<5, 1, 2>] := 1; // Type <5, 3, 1>

    elif D eq 8 then
	ellipticData[<2, 1, 1>] := 2;
	ellipticData[<3, 1, 1>] := 1;
	ellipticData[<3, 1,-1>] := 1;
	ellipticData[<4, 1, 1>] := 1;
	ellipticData[<4, 1,-1>] := 1;

    elif D eq 12 then

	B := Component(Gamma);

	if HasTotallyPositiveGenerator(B) then
	    ellipticData[<2, 1, 1>] := 3;
	    ellipticData[<3, 1, 1>] := 2;
	    ellipticData[<3, 1,-1>] := 0;
	    ellipticData[<6, 1,-1>] := 1;

	else
	    ellipticData[<2, 1, 1>] := 3;
	    ellipticData[<3, 1, 1>] := 0;
	    ellipticData[<3, 1,-1>] := 2;
	    ellipticData[<6, 1, 1>] := 1;

	end if;
    end if;

    Gamma`EllipticPointData := ellipticData;
    return ellipticData;
end intrinsic;

intrinsic NumberOfEllipticPoints(Gamma::GrpHilbert) -> RngIntElt
{}
    return #EllipticPointData(Gamma);
end intrinsic;

intrinsic NumberOfEllipticPoints(Gamma::GrpHilbert, singType::Tup) -> RngIntElt
{}
    boo, val := IsDefined(Gamma, singType);
    return boo select val else 0;
end intrinsic;


/////////////////////////////////////////////////////////////////////////////////
//
// Basic properties.
//
/////////////////////////////////////////////////////////////////////////////////

intrinsic IndexOfPrincipalCongruenceSubgroup(F::FldNum, N::RngOrdIdl) -> RngIntElt
{Return the index of the principal congruence subgroup of level `N` within the
full Hilbert modular group.}
    n := Norm(N);
    if n eq 1 then return 1; end if;

    index := 1;
    for ff in Factorization(n) do
        q := ff[1]^ff[2];
        index *:= q * (q^2 - 1);
    end for;
    return n;
end intrinsic;

intrinsic IndexOfGamma0(F::FldNum, N::RngOrdIdl) -> RngIntElt
{Return the index of the principal congruence subgroup of level `N` within the
full Hilbert modular group.}
    n := Norm(N);
    if n eq 1 then return 1; end if;

    index := 1;
    for ff in Factorization(n) do
        q := ff[1]^ff[2];
        index *:= (q + 1);
    end for;    
    return index;
end intrinsic;

intrinsic IndexOfGamma1(F::FldNum, N::RngOrdIdl) -> RngIntElt
{Return the index of the principal congruence subgroup of level `N` within the
full Hilbert modular group.}
    n := Norm(N);
    if n eq 1 then return 1; end if;
    
    index := 1;
    for ff in Factorization(n) do
        q := ff[1]^ff[2];
        index *:= q * (q + 1);
    end for;    
    return index;
end intrinsic;


intrinsic IsPrincipalCongruenceSubgroup(Gamma::GrpHilbert) -> BoolElt
{}
    return Index(Gamma) eq IndexOfPrincipalCongruenceSubgroup(Field(Gamma), Level(Gamma));
end intrinsic;

intrinsic IsTorsionFree(Gamma::GrpHilbert) -> BoolElt
{Determine if Gamma has torsion}
    return #EllipticPointData(Gamma) eq 0;
end intrinsic;


/////////////////////////////////////////////////////////////////////////////////
//
// Parabolic points (i.e., cusps)
//
/////////////////////////////////////////////////////////////////////////////////

////////// Functions for cusps  //////////

intrinsic NumberOfCusps(Gamma::GrpHilbert) -> RngIntElt
{Computes the number of cusps of Gamma_0(N).}

    error "Congruence Subgroup of the form Gamma_0(N) not implemented.";

    // Create the HMF ring.
    F := Field(Gamma);
    N := Level(Gamma);
    prec := 20; // This should be irrelevant.
    M := GradedRingOfHMFs(F, prec);
    Mn := HMFSpace(M, N, [k : k in [1..Degree(F)]]);

    // Return the number of cusps.
    return NumberOfCusps(Mn); // TODO: XXX:
end intrinsic;

intrinsic NumberOfParabolicPoints(Gamma::GrpHilbert) -> RngIntElt
{Return the number of cusps of the Hilbert modular surface associated to Gamma.}
    return NumberOfCusps(Gamma);
end intrinsic;

intrinsic Cusps(Gamma::GrpHilbert) -> SeqEnum
{Return the cusps of X_Gamma as a sequence of points in a projective space.}
    return Cusps(Level(Gamma), Component(Gamma) : GammaType := GammaType(Gamma));
end intrinsic;
