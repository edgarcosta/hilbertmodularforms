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
  GaloisDescent := true,
  SaveAndLoad := false,
  SaveDir := "./Precomputations/"
  ) -> SeqEnum[ModFrmHilDElt]
  {
    input:
      Mk: A space of HMFs
      // TODO abhijitm describe the optional parameters 
    returns: 
      A list of forms spanning the space of new cusp forms
  }
  if not assigned Mk`NewCuspFormBasis then
    // if SaveAndLoad is true, we try to load the new cusp basis from
    // the Precomputations/ folder
    if SaveAndLoad and GaloisDescent then
      loadfile_name := SaveDir cat SaveFilePrefix(Mk) cat "_cusp_newspace";
      is_saved, loadfile := OpenTest(loadfile_name, "r");
      loaded := false;
      if is_saved then
        loaded, newform_basis := LoadBasis(loadfile_name, Mk);
      end if;
      // loaded is false if the file was not saved or if
      // the precision of the stored basis wasn't high enough
      if loaded then
        Mk`NewCuspFormBasis := newform_basis;
      else
        Mk`NewCuspFormBasis := NewCuspForms(Mk);
        SaveBasis(loadfile_name, Mk`NewCuspFormBasis);
      end if;
    else
      Mk`NewCuspFormBasis := NewCuspForms(Mk : GaloisDescent := GaloisDescent);
    end if;
  end if;

  return SubBasis(Mk`NewCuspFormBasis, IdealClassesSupport, Symmetric);
end intrinsic;




intrinsic CuspFormBasisViaTrace(Mk::ModFrmHilD : IdealClassesSupport:=false, fail_counter := 10) -> SeqEnum[ModFrmHilDElt]
  {Returns a cuspform basis for the space Mk. Optional parameters: IdealClassesSupport - Compute a basis of forms on just a single component}
  /* Notes: Ben - We select the first n ideals (n = dimension of cusp space) ordered by norm for the traceforms. I tried ordering by trace as well, 
  but did not see a noticeable difference in the running times. Is there a good way to pick ideals for the traceforms? */

  // Initialize
  M := Parent(Mk);
  NN := Level(Mk);
  k := Weight(Mk);
  chi := Character(Mk);
  F := BaseField(Mk);
  ZF := Integers(F);
  C := NarrowClassGroupReps(M);
  dim := CuspDimension(Mk); // Change this to : version := "trace" later
  Ideals := IdealsUpTo(500,F); // Ideals for traceforms 
  _, ii := Modulus(chi); // Modulus

  // Components
  /* This is for computing trace forms that are only supported on a single component of the narrow class group. This is only relevent when the narrow class group is nontrivial. This can be ignored if IdealClassesSupport == False. 
  IdealClassesSupport := (IdealClassesSupport cmpeq false) select C else IdealClassesSupport; 
  if IdealClassesSupport ne C then 
    require #IdealClassesSupport eq 1 and IdealClassesSupport[1] in C: "IdealClassesSupport should be a single narrow class group representatives";
    require dim mod #C eq 0: "Narrow class group components do not have the same dimension!";
    require IsTrivial(chi): "Traceforms for nontrivial characters are not on a single component";
    dim div:= #C;
    bb := IdealClassesSupport[1];
    DD := Different(ZF);
    bbsharp := (bb * DD)^(-1);
    Ideals := [i : i in Ideals | IsNarrowlyPrincipal(i * bbsharp)];
  end if;
  */

  // Oldforms
  /* FIXME - This does not support components yet. Ben - If we are trying to compute forms on a specific component bb of Mk(NN,chi), I believe that we need to compute forms supported on a **different component bb'** of Mk(dd,chi) where dd | NN such that it maps to the correct component under the inclusion map. */
  B := [];
  Old := [ dd : dd in Divisors(NN) | dd ne NN ];
  for dd in Old do
    chidd := Restrict(chi, dd, ii);
    Mkdd  := HMFSpace(M, dd, k, chidd);
    B cat:= &cat[ Inclusion(f,Mk) : f in $$(Mkdd : IdealClassesSupport:=IdealClassesSupport) ];
    // Remove linear dependent forms 
    B := (#B ne 0) select Basis(B) else B;
  end for;

  /* We add one new trace forms one at a time. Remark: PrecomputeTraceForms(M,[aa]) checks if the computation has been done before. If the precomputation has not been done, it only computes class numbers that have not been precomputed */
  t := #B + 1;
  fails := 0; 
  while #B lt dim do

    d := dim - #B;
    aas := Ideals[t..t+d];
    t +:= d;
    
    // Compute new ideal
    aa := Ideals[t];
    vprintf HilbertModularForms: "Computing %o new traceforms.\n Fail counter: %o\n Ideals: %o\n", d, fails, [ IdealOneLine(aa) : aa in aas]; 
    PrecomputeTraceForms(M, aas);
    
    // Check for linear dependence
    B cat:= [TraceForm(Mk,aa) : aa in aas];
    B := (#B ne 0) select Basis(B) else B;
    if d eq (dim - #B) then
      fails +:=1;
    else
      fails := 0;
    end if;
    require fails lt fail_counter : "Hit %o fails. Need more precision for graded ring", fails;
  end while;

  // sanity check
  assert #B eq dim;

  return B;
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
  else
    k := Weight(Mk)[1];
    Mk`EisensteinBasis := NewEisensteinBasis(Mk) cat OldEisensteinBasis(Mk);
    require #Mk`EisensteinBasis eq EisensteinDimension(Mk) : "#Mk`EisensteinBasis = %o != %o = EisensteinDimension(Mk)", #Mk`EisensteinBasis, EisensteinDimension(Mk);
  end if;
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
