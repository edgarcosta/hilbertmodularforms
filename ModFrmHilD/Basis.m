///////////////////////////////////////////////////
//                                               //
//               Basis for M_k(N)                //
//                                               //
///////////////////////////////////////////////////

//Auxiliary function to handle the optional parameters for Basis calls

function SubBasis(basis, IdealClassesSupport, Symmetric)
  if IsNull(basis) then return basis; end if;
  IdealClassesCopy:=IdealClassesSupport;
  Mk := Parent(basis[1]);
  // handle optional argument IdealClassesSupport
  if IdealClassesSupport cmpeq false then
    IdealClassesSupport := SequenceToSet(NarrowClassGroupReps(Parent(Mk))); // Default is all ideals classes
  else
    IdealClassesSupport := SequenceToSet(IdealClassesSupport); // Optionally we may specify a subset of ideal classes
  end if;
  IdealClassesSupportComplement := Setseq(SequenceToSet(NarrowClassGroupReps(Parent(Mk))) diff IdealClassesSupport);

  if #IdealClassesSupportComplement eq 0 then // in this case LinearDependence will return the identity matrix
    basis := basis;
  else
    B := basis;
    relations := LinearDependence(B : IdealClasses:=IdealClassesSupportComplement);
    // basis is only supported over IdealClassesSupport
    basis := [ &+[rel[i]*B[i] : i in [1..#B]] : rel in relations];
  end if;

  // handle optional argument Symmetric
  if Symmetric then
    InvariantGenerators := [Symmetrize(b) : b in basis];
    coeffs := CoefficientsMatrix(InvariantGenerators : IdealClasses:=IdealClassesCopy);
    basis := [InvariantGenerators[i] : i in PivotRows(coeffs)];
  end if;
  return basis;
end function;

// Currently calls the Newforms and Eisenstein series from Creations folder

intrinsic CuspFormBasis(
  Mk::ModFrmHilD
  :
  IdealClassesSupport:=false,
  Symmetric:=false,
  GaloisDescent:=true) -> SeqEnum[ModFrmHilDElt]
  {returns a basis for cuspspace of M of weight k}

  require #SequenceToSet(Weight(Mk)) eq 1: "We only support parallel weight.";

  if not assigned Mk`CuspFormBasis then
    N := Level(Mk);
    k := Weight(Mk);

    // If a new subspace return only the newforms
    if IsNew(Mk) then
	Mk`CuspFormBasis := NewCuspForms(Mk : GaloisDescent:=GaloisDescent);
	if #Mk`CuspFormBasis gt 0 then
            dim := &+[Degree(CoefficientRing(f)) : f in Mk`CuspFormBasis];
	end if;
	require CuspDimension(Mk) eq dim : Sprintf("CuspDimension(Mk) = %o != %o = #Mk`CuspFormBasis", CuspDimension(Mk), #Mk`CuspFormBasis);
	return SubBasis(Mk`CuspFormBasis, IdealClassesSupport, Symmetric);
    end if;
    
    if k[1] ge 2 then
      Mk`CuspFormBasis := [];
      // This only works for trivial character, as we rely on the magma functionality
      require IsTrivial(DirichletRestriction(Character(Mk))): "We only support CuspFormBasis for characters with trivial dirichlet restriction, as we rely on the magma functionality";
      for dd in Divisors(N) do
        Mkdd := HMFSpace(Parent(Mk), dd, k);
        if CuspDimension(Mkdd) gt 0 then
          if dd eq N then
            Mk`CuspFormBasis cat:= NewCuspForms(Mk : GaloisDescent:=GaloisDescent);
          else
            Mk`CuspFormBasis cat:= OldCuspForms(Mkdd, Mk : GaloisDescent:=GaloisDescent);
          end if;
        end if;
      end for;
      dim := 0;
      if #Mk`CuspFormBasis gt 0 then
        dim := &+[Degree(CoefficientRing(f)) : f in Mk`CuspFormBasis];
      end if;
      require CuspDimension(Mk) eq dim : Sprintf("CuspDimension(Mk) = %o != %o = #Mk`CuspFormBasis", CuspDimension(Mk), #Mk`CuspFormBasis);
    else
      Mk`CuspFormBasis := HeckeStabilityCuspBasis(Mk);
    end if;
  end if;
  return SubBasis(Mk`CuspFormBasis, IdealClassesSupport, Symmetric);
end intrinsic;


intrinsic EisensteinBasis(
  Mk::ModFrmHilD
  :
  IdealClassesSupport:=false,
  Symmetric:=false
  ) -> SeqEnum[ModFrmHilDElt]
  { return a basis for the complement to the cuspspace of Mk }
  if not assigned Mk`EisensteinBasis then
    if IsCuspidal(Mk) then
	Mk`EisensteinBasis := [];
    else
	pairs := EisensteinAdmissibleCharacterPairs(Mk);
	eisensteinbasis := &cat[EisensteinInclusions(Mk, p[1], p[2]) : p in pairs];
	Mk`EisensteinBasis := &cat[GaloisOrbitDescent(f) : f in eisensteinbasis];
    end if;
    require #Mk`EisensteinBasis eq EisensteinDimension(Mk) : "#Mk`EisensteinBasis = %o != %o = EisensteinDimension(Mk)", #Mk`EisensteinBasis, EisensteinDimension(Mk);
  end if;

  // this handles the optional parameters
  return SubBasis(Mk`EisensteinBasis, IdealClassesSupport, Symmetric);
end intrinsic;




intrinsic Basis(
  Mk::ModFrmHilD
  :
  IdealClassesSupport:=false,
  Symmetric:=false
  ) -> SeqEnum[ModFrmHilDElt]
  { returns a Basis for the space }
  if not assigned Mk`Basis then
    vprintf HilbertModularForms: "Computing basis for space of parallel weight %o with precision %o\n", Weight(Mk)[1], Precision(Parent(Mk));
    // Cuspforms
    CB := CuspFormBasis(Mk);
    //Eisenstein Series
    EB := EisensteinBasis(Mk);
    Mk`Basis := EB cat CB;
  end if;

  // this handles the optional parameters
  return SubBasis(Mk`Basis, IdealClassesSupport, Symmetric);
end intrinsic;

intrinsic SymmetricBasis(
  Mk::ModFrmHilD
  :
  IdealClassesSupport:=false
  ) -> SeqEnum[ModFrmHilDElt]
  {returns a basis for the invariant subspace under the automorphisms of F}
  if not assigned Mk`Basis then
    vprintf HilbertModularForms: "Computing symmetric basis for space of parallel weight %o with precision %o\n", Weight(Mk)[1], Precision(Parent(Mk));
    // Cuspforms
    CB := CuspFormBasis(Mk);
    //Eisenstein Series
    EB := EisensteinBasis(Mk);
    Mk`Basis := EB cat CB;
  end if;
  return SubBasis(Mk`Basis, IdealClassesSupport, true);
end intrinsic;

intrinsic ComponentBasis(Mk::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  {returns a Basis for Mk of forms that are only supported on one component}
  bbs := NarrowClassGroupReps(Parent(Mk));
  return &cat[Basis(Mk: IdealClassesSupport := [bb]) : bb in bbs];
end intrinsic;

intrinsic SpecifiedComponentBasis(Mk::ModFrmHilD, bb::RngOrdIdl) -> SeqEnum[ModFrmHilDElt]
  {returns a basis of forms that are only supported on a specified component bb}
  return Basis(Mk: IdealClassesSupport := [bb]);
end intrinsic;
