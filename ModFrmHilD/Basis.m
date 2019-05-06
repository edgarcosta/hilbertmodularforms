///////////////////////////////////////////////////
//                                               //
//               Basis for M_k(N)                //
//                                               //
///////////////////////////////////////////////////

// Currently calls the Newforms and Eisenstein series from Creations folder


intrinsic CuspFormBasis(Mk::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  {returns a basis for cuspspace of M of weight k}
  N := Level(Mk);
  k := Weight(Mk);
  Cuspbasis := [];
  // This only works for trivial character, as we rely on the magma functionality
  assert Character(Mk) eq HeckeCharacterGroup(N)!1;
  for dd in Divisors(N) do
    Mkdd := HMFSpace(Parent(Mk), dd, k);
    // We are taking the Q orbits
	  NewSpace_dd := &cat[GaloisOrbitDescent(f) : f in NewformsToHMF(Mkdd)];
    OldSpace_dd := &cat[Inclusion(elt, Mk) : elt in NewSpace_dd ];
    Cuspbasis cat:= OldSpace_dd;
  end for;
  return Cuspbasis;
end intrinsic;


//TODO
// Only implemented for parallel weight 
intrinsic EisensteinBasis(Mk::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  { returns a basis for the complement to the cuspspace of M of weight k }
  M := Parent(Mk);
  NN := Level(Mk);
  k := Weight(Mk);
  require #SequenceToSet(k) eq 1: "Only implemented for parallel weight";
  require k[1] mod 2 eq 0: "Only implemented for even weight";  // Eisenstein series will work for parallel weight 1. 
  F := BaseField(Mk);
  ZF := Integers(F);
  n := Degree(ZF);
  HCG := HeckeCharacterGroup(1*Integers(F),[1..n]);
  DDs := [DD : DD in Divisors(NN) | DD^2 in Divisors(NN)];  // list NN1^2 | NN
  EB := [];  // Eisenstein basis, to be filled in
  // loop over
  for DD in DDs do 
    Mk_DD := HMFSpace(M, DD, k);
    HCGDD := HeckeCharacterGroup(DD,[1..n]);
    HCGDD_Elts := Elements(HCGDD);
    for eta in HCGDD_Elts do
      psi := (Restrict(eta, HCG))^(-1);
      E := EisensteinSeries(Mk_DD, eta, psi);
      EG := GaloisOrbitDescent(E); // Q orbits
      for elt in EG do
        EB cat:= Inclusion(elt,Mk); // Inclusion Mk_NN1 -> Mk
      end for;
    end for;
  end for;
  return EB;
end intrinsic;


intrinsic AllEisensteinBasis(Mk::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  { returns a basis for the complement to the cuspspace of M of weight k }
  M := Parent(Mk);
  NN := Level(Mk);
  k := Weight(Mk);
  require #SequenceToSet(k) eq 1: "Only implemented for parallel weight";
  require k[1] mod 2 eq 0: "Only implemented for even weight";  // Eisenstein series will work for parallel weight 1. 
  F := BaseField(Mk);
  ZF := Integers(F);
  n := Degree(ZF);
  EB := [];  // Eisenstein basis, to be filled in
  Characters := HeckeCharacterGroup(1*Integers(F),[1..n]);
  // loop over
  // In Cohen Stroemberg they divide into two cases based on k = 2 or 4. 
  // For k = 2, then I don't think Theorem 7.5.21 works. Take N = 1, then we get 1 form from G(X1,X1bar) from the non trivial character and nothing else. But there are generally 2 forms
  for NN1 in Divisors(NN) do 
    Mk_NN1 := HMFSpace(M, NN1, k);
    Characters_NN1 := Elements(HeckeCharacterGroup(NN1,[1..n]));
    //PrimitiveCharacters_NN1 := [elt : elt in Elements(HeckeCharacterGroup(NN1,[1..n])) | IsPrimitive(elt)];
    for eta in Characters_NN1 do
      psi := (Restrict(eta, Characters))^(-1);
      E := EisensteinSeries(Mk_NN1, eta, psi);
      EG := GaloisOrbitDescent(E); // Q orbits
      EB cat:= [Inclusion(elt,Mk) : elt in EG]; // Inclusion Mk_NN1 -> Mk
    end for;
  end for;
  return EB;
end intrinsic;


intrinsic Basis(Mk::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  { returns a Basis for the space }
  // Cuspforms
  CB := CuspFormBasis(Mk);
  //Eisenstein Series
  EB := EisensteinBasis(Mk);
  return EB cat CB;
end intrinsic;


/* intrinsic GaloisInvariantBasis(M::ModFrmHilD, N::RngOrdIdl, k::SeqEnum[RngIntElt]) -> SeqEnum[ModFrmHilDElt] */
/*   {returns a basis for the GaLois invariant subspace} */
/*   B:=Basis(M,N,k); */
/*   InvariantGenerators:=[]; */
/*   for x in B do */
/*     Append(~InvariantGenerators, 1/2*(x+Swap(x))); */
/*   end for; */
/*   InvariantBasis:=[]; */
/*   for x in InvariantGenerators do */
/*     if #LinearDependence(InvariantBasis cat [x]) eq 0 then */
/*       Append(~InvariantBasis, x); */
/*     end if; */
/*   end for; */
/*   return InvariantBasis; */
/* end intrinsic; */
