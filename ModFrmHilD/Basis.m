///////////////////////////////////////////////////
//                                               //
//               Basis for M_k(N)                //
//                                               //
///////////////////////////////////////////////////

// Currently calls the Newforms and Eisenstein series from Creations folder


intrinsic CuspFormBasis(Sp::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  {returns a basis for cuspspace of M of weight k}
  N := Level(Sp);
  k := Weight(Sp);
  Cuspbasis := [];
  // should we sieve instead? There isn't a significant difference for N small
  for dd in Divisors(N) do
	 NewSpace_dd := &cat[GaloisOrbitDescent(f) : f in NewformsToHMF(Sp)]; // We are taking the Q orbits
    OldSpace_dd := &cat[Inclusion(elt,Sp) : elt in NewSpace_dd ];
    Cuspbasis cat:= OldSpace_dd;
  end for;
  return Cuspbasis;
end intrinsic;


//TODO
// - Test for correctness
// - Clean up code?
intrinsic EisensteinBasis(Sp::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  { returns a basis for the complement to the cuspspace of M of weight k }
  N := Level(Sp);
  k := Weight(Sp);
  assert k gt 1; // Not implemented for k = 1 currently
  ZF := Integers(Sp);
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
          E := EisensteinSeries(Sp, eta, psi);
          EB cat:= GaloisOrbitDescent(E);
        end if;
      else
        // This does not function for k = 1 currently
        if Set([Component(H_psi,i) eq Component(eta,i) : i in [1..n]]) eq {false} then
          E := EisensteinSeries(Sp, eta, psi);
          EB cat:= GaloisOrbitDescent(E);
        end if;
      end if;
    end for;
  end for;
  return EB;
end intrinsic;



intrinsic Basis(Sp::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  { returns a Basis for the space }
  // Cuspforms
  CB := CuspFormBasis(Sp);
  //Eisenstein Series
  EB := EisensteinBasis(Sp);
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
