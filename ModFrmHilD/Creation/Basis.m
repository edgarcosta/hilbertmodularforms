// TODO: narrow>1
/* intrinsic Basis(M::ModFrmHilD, N::RngOrdIdl, k::SeqEnum[RngIntElt]) -> SeqEnum[ModFrmHilDElt], RngIntElt */
/*   { returns a Basis for the space } */
/*   CB, newforms_dimension := CuspFormBasis(M, N, k); */
/*   H := HeckeCharacterGroup(N); */
/*   //FIXME this is wrong for level not 1! */
/*   //print "FIXME this is wrong for level not 1!"; */
/*   eta := H ! 1; */
/*   // psi := H ! 1; */
/*   psi := eta; */
/*   E := EisensteinSeries(M, N, eta, psi, k); */
/*   return [E] cat CB, newforms_dimension; */
/* end intrinsic; */


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