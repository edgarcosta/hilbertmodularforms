
/////////////////////////////////////////////////////
//
//    Type Hook
//
/////////////////////////////////////////////////////

// This is a dummy type so that when general congruence
// subgroups are implemented, the functionality can be
// hooked in easily.

declare type StupidCongruenceSubgroup;
declare attributes StupidCongruenceSubgroup : Field,
	PrintString,
	Level,
	Index,
	EllipticPointData,
	ComponentIdeal,
	GammaType;

/////////////////// Creation ///////////////////

intrinsic CongruenceSubgroup(F::FldNum) -> StupidCongruenceSubgroup
{Create a dummy type. This is a placeholder for a future CongruenceSubgroup type.}
    return CongruenceSubgroup(F, 1*MaximalOrder(F));
end intrinsic;

intrinsic CongruenceSubgroup(F::FldNum, N::RngOrdIdl) -> StupidCongruenceSubgroup
{Create a dummy type. This is a placeholder for a future CongruenceSubgroup type.}
    return CongruenceSubgroup(F, N, 1*MaximalOrder(F));
end intrinsic;

intrinsic CongruenceSubgroup(F::FldNum, N::RngQuad) -> StupidCongruenceSubgroup
{}
    if N eq 1*MaximalOrder(F) then
	return CongruenceSubgroup(F);
    else
	error "CongruenceSubgroup not implemented for arbitrary orders.";
    end if;
end intrinsic;

intrinsic CongruenceSubgroup(F::FldNum, N::RngOrdIdl, B::RngOrdIdl) -> StupidCongruenceSubgroup
{Create a dummy type. This is a placeholder for a future CongruenceSubgroup type.
The B refers to the component, i.e., whether it is a subgroup of Gamma(O_F + B). }
    
    isRealQuadraticField := Degree(F) eq 2 and BaseRing(F) eq Rationals() and Discriminant(F) gt 0;
    require isRealQuadraticField: "Number field must be Real Quadratic Field.";

    Gamma := New(StupidCongruenceSubgroup);
    Gamma`Field := F;
    Gamma`ComponentIdeal := B;
    Gamma`Level := N;
    Gamma`Index := IndexOfPrincipalCongruenceSubgroup(F, N);
    Gamma`GammaType := "Gamma";
    return Gamma;
end intrinsic;


// At the moment, this is the only way to create a group of type Gamma_0(N).
intrinsic Gamma0(F::FldNum) -> StupidCongruenceSubgroup
{Return the Hilbert Modular group over `F`.}
    return CongruenceSubgroup(F);
end intrinsic;

// At the moment, this is the only way to create a group of type Gamma_0(N).
intrinsic Gamma0(F::FldNum, N::RngOrdIdl) -> StupidCongruenceSubgroup
{Return the Congruence Subgroup Gamma_0(N) over the number field `F`.}
    if N eq 1*MaximalOrder(F) then
	return CongruenceSubgroup(F);
    else
	G := CongruenceSubgroup(F, N);

	// Reassign all the important information.
	G`GammaType := "Gamma_0";
	G`Index := IndexOfGamma0(F, N);
	return G;
    end if;
end intrinsic;

/////////////////// Printing ///////////////////



intrinsic Print(Gamma::StupidCongruenceSubgroup)
{Print.}
    print "Congruence Subgroup of Hilbert Modular group.";
    print "Field:", Field(Gamma);
    printf "Level: (%o)\n", IdealOneLine(Level(Gamma));
    printf "Component: (%o)\n", IdealOneLine(Component(Gamma));
    print "Index: ", Index(Gamma);
    print "Gamma Type:", GammaType(Gamma);
    return;
end intrinsic;


////////// StupidCongruenceSubgroup access to attributes //////////

intrinsic Level(Gamma::StupidCongruenceSubgroup) -> RngOrdIdl
{Return the Level attribute}
    return Gamma`Level;
end intrinsic;

intrinsic Field(Gamma::StupidCongruenceSubgroup) -> FldNum
{Return the Level attribute}
    return Gamma`Field;
end intrinsic;

intrinsic Index(Gamma::StupidCongruenceSubgroup) -> RngIntElt
{Return the Index Attribute.}
    return Gamma`Index;
end intrinsic;

intrinsic ComponentIdeal(Gamma::StupidCongruenceSubgroup) -> RngOrdIdl
{Return the ComponentIdeal Attribute. That is, \frak(b), the ideal indexing the 
component of the Hilbert Modular Surface}
    return Gamma`ComponentIdeal;
end intrinsic;

intrinsic Component(Gamma::StupidCongruenceSubgroup) -> RngIntElt
{Return the ComponentIdeal Attribute. That is, \frak(b), the ideal indexing the 
component of the Hilbert Modular Surface}
    return ComponentIdeal(Gamma);
end intrinsic;

intrinsic GammaType(Gamma::StupidCongruenceSubgroup) -> MonStgElt
{}
    return Gamma`GammaType;
end intrinsic;
          

////////// Basic functionality //////////

intrinsic 'eq'(Gamma1::StupidCongruenceSubgroup, Gamma2::StupidCongruenceSubgroup) -> BoolElt
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

intrinsic EllipticPointData(Gamma::StupidCongruenceSubgroup) -> Assoc
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

intrinsic _EllipticPointDataSpecialCases(Gamma::StupidCongruenceSubgroup) -> Assoc
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

intrinsic NumberOfEllipticPoints(Gamma::StupidCongruenceSubgroup) -> RngIntElt
{}
    return #EllipticPointData(Gamma);
end intrinsic;

intrinsic NumberOfEllipticPoints(Gamma::StupidCongruenceSubgroup, singType::Tup) -> RngIntElt
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
    q := Norm(N);
    if q eq 1 then return 1; end if;
    
    assert IsPrimePower(q);
    return q * (q^2 - 1);
end intrinsic;

intrinsic IndexOfGamma0(F::FldNum, N::RngOrdIdl) -> RngIntElt
{Return the index of the principal congruence subgroup of level `N` within the
full Hilbert modular group.}
    q := Norm(N);
    if q eq 1 then return 1; end if;
    
    assert IsPrimePower(q);
    return q + 1;
end intrinsic;


intrinsic IsPrincipalCongruenceSubgroup(Gamma::StupidCongruenceSubgroup) -> BoolElt
{}
    return Index(Gamma) eq IndexOfPrincipalCongruenceSubgroup(Field(Gamma), Level(Gamma));
end intrinsic;

intrinsic IsTorsionFree(Gamma::StupidCongruenceSubgroup) -> BoolElt
{Determine if Gamma has torsion}
    return #EllipticPointData(Gamma) eq 0;
end intrinsic;


/////////////////////////////////////////////////////////////////////////////////
//
// Parabolic points (i.e., cusps)
//
/////////////////////////////////////////////////////////////////////////////////

////////// Functions for cusps  //////////

intrinsic NumberOfCusps(Gamma::StupidCongruenceSubgroup) -> RngIntElt
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

intrinsic NumberOfParabolicPoints(Gamma::StupidCongruenceSubgroup) -> RngIntElt
{Return the number of cusps of the Hilbert modular surface associated to Gamma.}
    return NumberOfCusps(Gamma);
end intrinsic;

intrinsic Cusps(Gamma::StupidCongruenceSubgroup) -> SeqEnum
{Return the cusps of X_Gamma as a sequence of points in a projective space.}
    return Cusps(Level(Gamma), Component(Gamma) : GammaType := GammaType(Gamma));
end intrinsic;
