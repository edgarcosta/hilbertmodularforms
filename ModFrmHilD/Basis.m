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
  aas := [aa : aa in Divisors(NN) | aa^2 in Divisors(NN)]; 
  EB := [];  // Eisenstein basis, to be filled in
  for aa in aas do // loop over
    N0 := aa^2;
    Mk_N0 := HMFSpace(M, N0, k);
    HCGaa := HeckeCharacterGroup(aa,[1..n]);
    PrimitiveCharacters := [elt : elt in Elements(HCGaa) | IsPrimitive(elt)];
    if aa eq 1*ZF then // Hack to add trivial character back in (It is imprimitive!)
      Append(~PrimitiveCharacters, HCGaa!1);
    end if;
    for eta in PrimitiveCharacters do
      psi := eta^(-1);
      E := EisensteinSeries(Mk_N0, eta, psi);
      EG := GaloisOrbitDescent(E); // Q orbits
      EB cat:= &cat[Inclusion(elt,Mk) : elt in EG];
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
