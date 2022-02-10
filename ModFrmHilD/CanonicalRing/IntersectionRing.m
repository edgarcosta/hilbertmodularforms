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
//    Dispatch for Number Field Input.
//
/////////////////////////////////////////////////////

intrinsic ChernNumbersOfMinimalResolution(F::FldNum) -> SeqEnum
{Returns a tuple <c1^2, c2> corresponding to the Chern numbers of the 
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

  secondChernNumber := volumeOfGammaK + NumberOfCusps(Gamma);

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
  if not IsTorsionTrivial(Gamma) then
      // Placeholder.
      C1TorsionCorrectionTerms := -100;
      C2TorsionCorrectionTerms := -100;
      
      firstChernNumber +:= C1TorsionCorrectionTerms;
      secondChernNumber +:= C2torsionCorrectionTerms;

      error "Not Implemented when Gamma has torsion.";
  end if;
      
  return <"Not Implemented", secondChernNumber>;
end intrinsic;


intrinsic IntersectionRing(Gamma::StupidCongruenceSubgroup) -> Any
{Computes the Cohomology ring of the Bailey-Borel compactification of the Hilbert Modular Surface.}
    error "Not Implemented.";
end intrinsic;

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
// Test Intersection Ring
//
/////////////////////////////////////////////////////////////////////////////////

