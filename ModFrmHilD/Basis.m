///////////////////////////////////////////////////
//                                               //
//               Basis for M_k(N)                //
//                                               //
///////////////////////////////////////////////////

// Currently calls the Newforms and Eisenstein series from Creations folder

intrinsic CuspFormBasis(Mk::ModFrmHilD: verbose:=false) -> SeqEnum[ModFrmHilDElt]
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

        if verbose then
          printf "Cusp old form basis in level of norm %o computed with precision %o (default prec = %o)\n", Norm(dd),  traceBoundIncl, Precision(Parent(Mk));
        end if;

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


intrinsic EisensteinBasis(Mk::ModFrmHilD: verbose:=false) -> SeqEnum[ModFrmHilDElt]
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

      if verbose then
        print "Eisenstein old basis in level  of norm ", Norm(N0),  "  computed with precision", traceBoundIncl;
      end if;

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

intrinsic Basis(Mk::ModFrmHilD: verbose:=false) -> SeqEnum[ModFrmHilDElt]
  { returns a Basis for the space }
  if not assigned Mk`Basis then
    if verbose then
      print "Wanted precision of space of parallel weight   ", Weight(Mk)[1], "     is", Precision(Parent(Mk));
    end if;
    // Cuspforms
    CB := CuspFormBasis(Mk);
    //Eisenstein Series
    EB := EisensteinBasis(Mk);
    Mk`Basis := EB cat CB;
  end if;


  return Mk`Basis;
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
  // Preliminaries
  M := Parent(Mk);
  B := Basis(Mk);
  bbs := NarrowClassGroupReps(M);
  NewBasis :=[];
  // Loop over ideal classes
  for i in [1..#bbs] do
    IC := Remove(bbs,i);
    L := LinearDependence(B : IdealClasses := IC);
    for relation in L do
      f := &+[relation[i]*B[i] : i in [1..#B]];
      NewBasis cat:= [f];
    end for;
  end for;
  return NewBasis;
end intrinsic;

intrinsic SpecifiedComponentBasis(Mk::ModFrmHilD, bb::RngOrdIdl) -> SeqEnum[ModFrmHilDElt]
  {returns a basis of forms that are only supported on a specified component bb}
  // Preliminaries
  M := Parent(Mk);
  B := Basis(Mk);
  bbs := NarrowClassGroupReps(M);
  NewBasis :=[];
  // Set i to be the component the you want to see
  i := Index(bbs,bb);
  IC := Remove(bbs,i);
  L := LinearDependence(B : IdealClasses := IC);
  for relation in L do
    f := &+[relation[i]*B[i] : i in [1..#B]];
    NewBasis cat:= [f];
  end for;
  return NewBasis;
end intrinsic;
