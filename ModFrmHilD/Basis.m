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

  if assigned Mk`CuspFormBasis then
    return Mk`CuspFormBasis;
  end if;

  k := Weight(Mk);

  // Weight 1 forms cannot be computed using Jacquet-Langlands transfer
  // The Magma functionality doesn't currently support nebentypus characters with nontrivial
  // Dirichlet restrictions, so that is also handled here. 
  if not &and[x ge 2 : x in k] or not IsTrivial(DirichletRestriction(Character(Mk))) then
    Mk`CuspFormBasis := HeckeStabilityCuspBasis(Mk);
  end if;

  Mk`CuspFormBasis := NewCuspFormBasis(Mk : GaloisDescent := GaloisDescent) cat OldCuspFormBasis(Mk : GaloisDescent := GaloisDescent);
  // The contents of Mk`CuspFormBasis should be a basis for the space of cuspforms
  require CuspDimension(Mk) eq #Mk`CuspFormBasis : Sprintf("CuspDimension(Mk) = %o != %o = #Mk`CuspFormBasis", CuspDimension(Mk), #Mk`CuspFormBasis);
  return SubBasis(Mk`CuspFormBasis, IdealClassesSupport, Symmetric);
end intrinsic;

intrinsic NewCuspFormBasis(
  Mk::ModFrmHilD 
  : 
  IdealClassesSupport := false,
  Symmetric := false,
  GaloisDescent := true) -> SeqEnum[ModFrmHilDElt]
  {
    input:
      Mk: A space of HMFs
      // TODO abhijitm describe the optional parameters 
    returns: 
      A list of forms spanning the space of new cusp forms
  }
  if not assigned Mk`NewCuspFormBasis then
    Mk`NewCuspFormBasis := NewCuspForms(Mk : GaloisDescent := GaloisDescent);
  end if;

  return SubBasis(Mk`NewCuspFormBasis, IdealClassesSupport, Symmetric);
end intrinsic;
  
intrinsic OldCuspFormBasis(
  Mk::ModFrmHilD 
  : 
  IdealClassesSupport := false,
  Symmetric := false,
  GaloisDescent := true) -> SeqEnum[ModFrmHilDElt]
  {
    input:
      Mk: A space of HMFs 
      // TODO abhijitm describe the optional parameters
    returns: 
      If N is the level of Mk, returns the inclusions of forms of level
      N' | N into Mk. These will always be linearly independent
      (in fact, orthogonal w/r/t the Petersson inner product),
      so we can take them as a basis directly.
  }
  if not assigned Mk`OldCuspFormBasis then
    M := Parent(Mk);
    N := Level(Mk);
    k := Weight(Mk);
    
    Mk`OldCuspFormBasis := [];
    divisors := Exclude(Divisors(N), N);
    for D in divisors do
      Mk_D := HMFSpace(M, D, k);
      Mk`OldCuspFormBasis cat:= &cat[Inclusion(f, Mk) : f in NewCuspFormBasis(Mk_D : IdealClassesSupport := IdealClassesSupport, Symmetric := Symmetric, GaloisDescent := GaloisDescent)];
    end for;
  end if;
  return SubBasis(Mk`OldCuspFormBasis, IdealClassesSupport, Symmetric);
end intrinsic;

intrinsic EisensteinBasis(
  Mk::ModFrmHilD
  :
  IdealClassesSupport:=false,
  Symmetric:=false
  ) -> SeqEnum[ModFrmHilDElt]
  {returns a basis for the space of Eisenstein series of Mk of }

  if assigned Mk`EisensteinBasis then
    return Mk`EisensteinBasis;
  end if;

  if not IsParallel(Weight(Mk)) then
    Mk`EisensteinBasis := [];
  end if;

  k := Weight(Mk)[1];
  Mk`EisensteinBasis := NewEisensteinBasis(Mk) cat OldEisensteinBasis(Mk);
  require #Mk`EisensteinBasis eq EisensteinDimension(Mk) : "#Mk`EisensteinBasis = %o != %o = EisensteinDimension(Mk)", #Mk`EisensteinBasis, EisensteinDimension(Mk);
  return SubBasis(Mk`EisensteinBasis, IdealClassesSupport, Symmetric);
end intrinsic;

intrinsic NewEisensteinBasis(
  Mk::ModFrmHilD
  :
  IdealClassesSupport:=false,
  Symmetric:=false
  ) -> SeqEnum[ModFrmHilDElt]
  {
    input:
      Mk: A space of HMFs
      // TODO abhijitm describe the optional parameters 
    returns: 
      A list of forms spanning the space of new Eisenstein series
  }

  if assigned Mk`NewEisensteinBasis then
	  return Mk`NewEisensteinBasis;
  else
    pairs := EisensteinAdmissibleCharacterPairs(Mk);
    Mk`NewEisensteinBasis := &cat[GaloisOrbitDescent(EisensteinSeries(Mk, pair[1], pair[2])) : pair in pairs];
  end if;

  // this handles the optional parameters
  return SubBasis(Mk`NewEisensteinBasis, IdealClassesSupport, Symmetric);
end intrinsic;
  
intrinsic OldEisensteinBasis(
  Mk::ModFrmHilD 
  : 
  IdealClassesSupport := false,
  Symmetric := false
  ) -> SeqEnum[ModFrmHilDElt]
  {
    input:
      Mk: A space of HMFs 
      // TODO abhijitm describe the optional parameters
    returns: 
      If N is the level of Mk, returns the inclusions of forms of level
      N' | N into Mk. These will always be linearly independent
      (in fact, orthogonal w/r/t the Petersson inner product),
      so we can take them as a basis directly.
  }
  
  if not assigned Mk`OldEisensteinBasis then
    M := Parent(Mk);
    N := Level(Mk);
    k := Weight(Mk);
    chi := Character(Mk);

    Mk`OldEisensteinBasis := [];

    // We want to iterate through divisors D of N from which an 
    // Eisenstein series with nebentypus chi could arise.
    // This means that we need Cond(chi) | D. We also exclude
    // D = N because we want oldforms.
    divisors := [D : D in Divisors(N) | (D ne N) and (D subset Conductor(chi))];
    for D in divisors do
      chi_D := Restrict(chi, D, [1,2]);
      Mk_D := HMFSpace(M, D, k, chi_D);
      Mk`OldEisensteinBasis cat:= &cat[Inclusion(f, Mk) : f in NewEisensteinBasis(Mk_D : IdealClassesSupport := IdealClassesSupport, Symmetric := Symmetric)];
    end for;
  end if;
  return SubBasis(Mk`OldEisensteinBasis, IdealClassesSupport, Symmetric);
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
