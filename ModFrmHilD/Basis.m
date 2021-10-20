///////////////////////////////////////////////////
//                                               //
//               Basis for M_k(N)                //
//                                               //
///////////////////////////////////////////////////

// Currently calls the Newforms and Eisenstein series from Creations folder

intrinsic CuspFormBasis(Mk::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  {returns a basis for cuspspace of M of weight k}
  if not assigned Mk`CuspFormBasis then
    N := Level(Mk);
    k := Weight(Mk);
    Cuspbasis := [];
    // This only works for trivial character, as we rely on the magma functionality
    assert Character(Mk) eq HeckeCharacterGroup(N)!1;
    for dd in Divisors(N) do
      Mkdd := HMFSpace(Parent(Mk), dd, k);
      dim:=Dimension(HilbertCuspForms(BaseField(Mk), dd, k));
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
  return Mk`CuspFormBasis;
end intrinsic;


intrinsic EisensteinBasis(Mk::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  { returns a basis for the complement to the cuspspace of M of weight k }
  if not assigned Mk`EisensteinBasis then
    M := Parent(Mk);
    NN := Level(Mk);
    k := Weight(Mk);
    require #SequenceToSet(k) eq 1: "Only implemented for parallel weight";
    require k[1] mod 2 eq 0: "Only implemented for even weight";  // Eisenstein series will work for parallel weight 1.
    F := BaseField(Mk);
    ZF := Integers(F);
    n := Degree(ZF);
    aas := [aa : aa in Divisors(NN) | aa^2 in Divisors(NN)];
    EB := [];  // Eisenstein basis, to be filled in
    for aa in aas do // loop over
      N0 := aa^2;
      Mk_N0 := HMFSpace(M, N0, k);
      traceBoundIncl:=TraceBoundInclusion(Mk_N0, Mk);

      vprintf HilbertModularForms: "Eisenstein old basis in level of norm %o computed with precision %o\n", Norm(N0), traceBoundIncl;

      HCGaa := HeckeCharacterGroup(aa,[1..n]);
      PrimitiveCharacters := [elt : elt in Elements(HCGaa) | IsPrimitive(elt)];
      if aa eq 1*ZF then // Hack to add trivial character back in (It is imprimitive!)
        Append(~PrimitiveCharacters, HCGaa!1);
      end if;
      for eta in PrimitiveCharacters do
        psi := eta^(-1);
        HigherPrecM:=GradedRingOfHMFs(BaseField(Mk), traceBoundIncl);
        HigherPrecMk_N0:=HMFSpace(HigherPrecM, N0, k);
        E := EisensteinSeries(HigherPrecMk_N0, eta, psi);
        EG := GaloisOrbitDescent(E); // Q orbits
        EB cat:= &cat[Inclusion(elt,Mk) : elt in EG];
      end for;
    end for;
    Mk`EisensteinBasis := EB;
  end if;
  return Mk`EisensteinBasis;
end intrinsic;

intrinsic Basis(Mk::ModFrmHilD: IdealClassesSupport := false) -> SeqEnum[ModFrmHilDElt]
  { returns a Basis for the space }
  if not assigned Mk`Basis then
    vprintf HilbertModularForms: "Computing basis for space of parallel weight %o with precision %o\n", Weight(Mk)[1], Precision(Parent(Mk));
    // Cuspforms
    CB := CuspFormBasis(Mk);
    //Eisenstein Series
    EB := EisensteinBasis(Mk);
    Mk`Basis := EB cat CB;
  end if;

  if IdealClassesSupport cmpeq false then
    IdealClassesSupport := SequenceToSet(NarrowClassGroupReps(Parent(Mk))); // Default is all ideals classes
  else
    IdealClassesSupport := SequenceToSet(IdealClassesSupport); // Optionally we may specify a subset of ideal classes
  end if;
  IdealClassesSupportComplement := IdealClassesSupport diff SequenceToSet(NarrowClassGroupReps(Parent(Mk)));
  if #IdealClassesSupportComplement eq 0 then // in this case LinearDependence will return the identity matrix
    return Mk`Basis;
  end if;
  B := Mk`Basis;
  relations := LinearDependence(B : IdealClasses := IdealClassesSupportComplement);
  res := [];
  for elt in relations do
    // f is only supported over IdealClassesSupport
    f := &+[elt[i]*B[i] : i in [1..#B]];
    Append(~res, f);
  end for;
  return res;
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
