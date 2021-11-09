///////////////////////////////////////////////////
//                                               //
//               Basis for M_k(N)                //
//                                               //
///////////////////////////////////////////////////

//Auxiliar function to handle the optional parameters for Basis calls
function SubBasis(basis, IdealClassesSupport, GaloisInvariant)
  if IsNull(basis) then return basis; end if;
  Mk := Parent(basis[1]);
  // handle optional argument IdealClassesSupport
  if IdealClassesSupport cmpeq false then
    IdealClassesSupport := SequenceToSet(NarrowClassGroupReps(Parent(Mk))); // Default is all ideals classes
  else
    IdealClassesSupport := SequenceToSet(IdealClassesSupport); // Optionally we may specify a subset of ideal classes
  end if;
  IdealClassesSupportComplement := SequenceToSet(NarrowClassGroupReps(Parent(Mk))) diff IdealClassesSupport;

  if #IdealClassesSupportComplement eq 0 then // in this case LinearDependence will return the identity matrix
    basis := basis;
  else
    B := basis;
    relations := LinearDependence(B : IdealClasses:=IdealClassesSupportComplement);
    // basis is only supported over IdealClassesSupport
    basis := [ &+[rel[i]*B[i] : i in [1..#B]] : rel in relations];
  end if;

  // handle optional argument GaloisInvariant
  if GaloisInvariant then
    InvariantGenerators := [1/2*(b + Swap(b)) : b in basis];
    coeffs := CoefficientsMatrix(basis : IdealClasses:=IdealClassesSupport);
    basis := [basis[i] : i in PivotRows(coeffs)];
  end if;
  return basis;
end function;

// Currently calls the Newforms and Eisenstein series from Creations folder

intrinsic CuspFormBasis(
  Mk::ModFrmHilD
  :
  IdealClassesSupport:=false,
  GaloisInvariant:=false) -> SeqEnum[ModFrmHilDElt]
  {returns a basis for cuspspace of M of weight k}
  if not assigned Mk`CuspFormBasis then
    N := Level(Mk);
    k := Weight(Mk);
    Cuspbasis := [];
    // This only works for trivial character, as we rely on the magma functionality
    require IsTrivial(Character(Mk)): "We only support CuspFormBasis  for trivial character, as we rely on the magma functionality";
    for dd in Divisors(N) do
      Mkdd := HMFSpace(Parent(Mk), dd, k);
      dim := Dimension(HilbertCuspForms(BaseField(Mk), dd, k));
      if dim gt 0 then
        traceBoundIncl:=TraceBoundInclusion(Mkdd, Mk);

        vprintf HilbertModularForms: "Cusp old form basis in level of norm %o computed with precision %o (default prec = %o)\n", Norm(dd),  traceBoundIncl, Precision(Parent(Mk));

        HigherPrecM:=GradedRingOfHMFs(BaseField(Mk), traceBoundIncl);
        HigherPrecMkdd:=HMFSpace(HigherPrecM, dd, k);
        // We are taking the Q orbits
        HigherPrecNewSpace_dd := &cat[GaloisOrbitDescent(f) : f in NewformsToHMF(HigherPrecMkdd)];
        OldSpace_dd := &cat[Inclusion(elt, Mk) : elt in HigherPrecNewSpace_dd];
        Cuspbasis cat:= OldSpace_dd;
      end if;
    end for;
    Mk`CuspFormBasis := Cuspbasis;
  end if;
  return SubBasis(Mk`CuspFormBasis, IdealClassesSupport, GaloisInvariant);
end intrinsic;


intrinsic EisensteinBasis(
  Mk::ModFrmHilD
  :
  IdealClassesSupport:=false,
  GaloisInvariant:=false) -> SeqEnum[ModFrmHilDElt]
  { returns a basis for the complement to the cuspspace of M of weight k }
  if not assigned Mk`EisensteinBasis then
    M := Parent(Mk);
    NN := Level(Mk);
    k := Weight(Mk);
    require #SequenceToSet(k) eq 1: "Only implemented for parallel weight";
    require k[1] mod 2 eq 0 or k[1] eq 1: "Only implemented for even weight or weigh 1";  // Eisenstein series will work for parallel weight 1.
    require IsTrivial(Character(Mk)): "Only implemented for trivial character";
    F := BaseField(Mk);
    ZF := Integers(F);
    n := Degree(ZF);
    aas := [aa : aa in Divisors(NN) | aa^2 in Divisors(NN)];
    EB := [];  // Eisenstein basis, to be filled in
    for aa in aas do // loop over
      N0 := aa^2; // N0 divides N
      Mk_N0 := HMFSpace(M, N0, k);
      traceBoundIncl := TraceBoundInclusion(Mk_N0, Mk);

      vprintf HilbertModularForms: "Eisenstein old basis in level of norm %o computed with precision %o\n", Norm(N0), traceBoundIncl;

      HCGaa := HeckeCharacterGroup(aa, [1..n]);
      PrimitiveCharacters := [elt : elt in Elements(HCGaa) | IsPrimitive(elt)];
      if aa eq 1*ZF then // Hack to add trivial character back in (It is imprimitive!)
        Append(~PrimitiveCharacters, HCGaa!1);
      end if;
      for eta in PrimitiveCharacters do
        // psi*eta = trivial
        psi := eta^(-1);
        // and Modulus(psi)*Modulos(eta) = aa^2 = N
        if traceBoundIncl gt Precision(M) then
          HigherPrecM := GradedRingOfHMFs(BaseField(Mk), traceBoundIncl);
          HigherPrecMk_N0 := HMFSpace(HigherPrecM, N0, k);
        else
          HigherPrecM := M;
          HigherPrecMk_N0 := Mk_N0;
        end if;
        E := EisensteinSeries(HigherPrecMk_N0, eta, psi);
        EG := GaloisOrbitDescent(E); // Q orbits
        EB cat:= &cat[Inclusion(elt, Mk) : elt in EG];
      end for;
    end for;
    Mk`EisensteinBasis := EB;
  end if;


  // this handles the optional parameters
  return SubBasis(Mk`EisensteinBasis, IdealClassesSupport, GaloisInvariant);
end intrinsic;




intrinsic Basis(
  Mk::ModFrmHilD
  :
  IdealClassesSupport:=false,
  GaloisInvariant:=false
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
  return SubBasis(Mk`Basis, IdealClassesSupport, GaloisInvariant);
end intrinsic;

intrinsic GaloisInvariantBasis(Mk::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  {returns a basis for the Galois invariant subspace}

  B := Basis(Mk);
  InvariantGenerators:=[];
  for x in B do
    Append(~InvariantGenerators, 1/2*(x+Swap(x)));
  end for;
  InvariantBasis:=[];
  for x in InvariantGenerators do
    if #LinearDependence(InvariantBasis cat [x]) eq 0 then
      Append(~InvariantBasis, x);
    end if;
  end for;
  return InvariantBasis;
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
