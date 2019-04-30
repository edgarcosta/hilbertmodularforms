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
    print "dd = ", dd, "\n", "Ns, Os, Cs = ", #NewSpace_dd, #OldSpace_dd, #Cuspbasis, "\n\n";
  end for;
  return Cuspbasis;
end intrinsic;


//TODO
// - Test for correctness
// - Clean up code?
intrinsic EisensteinBasis(Mk::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  { returns a basis for the complement to the cuspspace of M of weight k }
  N := Level(Mk);
  k := Weight(Mk);
  assert k[1] gt 1; // Not implemented for k = 1 currently
  ZF := Integers(Mk);
  n := Degree(ZF);
  EB := [];
  Hplus := HeckeCharacterGroup(1*ZF,[1..n]);
  HNplus := HeckeCharacterGroup(N,[1..n]);

  for i in [0..#Hplus-1] do
    eta := Hplus.i;
    for j in [0..#HNplus-1] do
      psi := HNplus.j;
      H_psi := Restrict(psi, Hplus);
      // This is checking the condition on pg 458
      if k[1] mod 2 eq 0 then
        if H_psi*eta^(-1) eq Hplus!1 then
          E := EisensteinSeries(Mk, eta, psi);
          EB cat:= GaloisOrbitDescent(E);
        end if;
      else
        // This does not function for k = 1 currently
        if Set([Component(H_psi,i) eq Component(eta,i) : i in [1..n]]) eq {false} then
          E := EisensteinSeries(Mk, eta, psi);
          EB cat:= GaloisOrbitDescent(E);
        end if;
      end if;
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
