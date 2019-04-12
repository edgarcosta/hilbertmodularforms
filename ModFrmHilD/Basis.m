///////////////////////////////////////////////////
//                                               //
//               Basis for M_k(N)                //
//                                               //
///////////////////////////////////////////////////

// Currently calls the Newforms and Eisenstein series from Creations folder


//TODO should we sieve? 
//BB - I removed the newform dimension. Do we use anywhere?      /* if dd eq N then newforms_dimension := #CuspSpace_dd; end if;  */
intrinsic CuspFormBasis(M::ModFrmHilD, N::RngOrdIdl, k::SeqEnum[RngIntElt]) -> SeqEnum[ModFrmHilDElt]
  {returns a basis for cuspspace of M of weight k}  
  Cuspbasis := []; 
  for dd in Divisors(N) do 
    NewSpace_dd := &cat[GaloisOrbitDescent(f) : f in NewformsToHMF(M, dd, k)]; 
    OldSpace_dd := &cat[Inclusion(elt,N) : elt in NewSpace_dd ]; 
    Cuspbasis cat:= OldSpace_dd; 
  end for; 
  return Cuspbasis; 
end intrinsic; 



//TODO - Test for correctness. Clean up code? 
intrinsic EisensteinBasis(M::ModFrmHilD, N::RngOrdIdl, k::SeqEnum[RngIntElt]) -> SeqEnum[ModFrmHilDElt]
  {returns a basis for the complement to the cuspspace of M of weight k}
  ZF := Integers(M);
  n := Degree(ZF);
  EB := [];
  for aa in Divisors(N) do 
    // HeckeCharactergroups takes places index by number i.e. [1,2,3] means take all 3 places for real field.
    // This is checking the condition on pg 458
    bb := N div aa;
    Haa := HeckeCharacterGroup(aa,[i : i in [1..n]]);
    Hbb := HeckeCharacterGroup(bb,[i : i in [1..n]]);
    H := HeckeCharacterGroup(1*ZF,[i : i in [1..n]]);
    for i in [0..#Haa-1] do 
      eta := Haa.i;
      H_eta := Restrict(eta, H); 
      for j in [0..#Hbb-1] do 
        psi := Hbb.j;
        H_psi := Restrict(psi, H);
        // This is checking the condition on pg 458
        if k[1] mod 2 eq 0 mod 2 then 
          if Set([Component(H_psi,i) eq Component(H_eta,i) : i in [1..n]]) eq {true} then
            E := EisensteinSeries(M, N, eta, psi, k);
            EB cat:= [E];
          end if;
        else
          if Set([Component(H_psi,i) eq Component(H_eta,i) : i in [1..n]]) eq {false} then
            E := EisensteinSeries(M, N, eta, psi, k);
            EB cat:= [E];
          end if;
        end if;
      end for;
    end for;
  end for;
  return EB;
end intrinsic;



//BB - I removed the newform dimension.       CB, newforms_dimension := CuspFormBasis(M, N, k);
intrinsic Basis(M::ModFrmHilD, N::RngOrdIdl, k::SeqEnum[RngIntElt]) -> SeqEnum[ModFrmHilDElt], RngIntElt 
  { returns a Basis for the space } 
  // Cuspforms
  CB := CuspFormBasis(M, N, k);
  //Eisenstein Series
  EB := EisensteinBasis(M, N, k);
  return CB cat EB;
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
