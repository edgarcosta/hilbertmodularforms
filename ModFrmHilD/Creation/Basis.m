

//Todo [Ben] This needs serious checking. We need to verify that inclusion map is defined correctly. Reference?

// Inclusion M_k(N) -> M_k(N1) for N1| N2 

intrinsic Inclusion(f::ModFrmHilDElt, N1::RngOrdIdl) -> SeqEnum[ModFrmHilDElt]
  {Includes a form f of level N into the space of level N1} 
  M := Parent(f);
  N := Level(f);
  k := Weight(f);
  assert N subset N1; // To contain is to divide
  bbs := NarrowClassGroupReps(M);
  mp := NarrowClassGroupMap(M);
  IncludedForms := [];
  for ee in Divisors(N1/N) do 
    coeff := Coefficients(f);
    for bb in bbs do
      bbee := mp((bb*ee)@@mp); // Representative of narrow class bbee := bb*ee
      for nn in Keys(coeff[bb]) do
        if nn*bb in Keys(coeff[bbee]) then
          coeff[bbee][nn*bb] := coeff[bb][nn];
        else 
          coeff[bbee][nn*bb] := 0;
        end if;
      end for;
    end for;
    Append(~IncludedForms, HMF(M, N1, k, coeff));
  end for;
  return IncludedForms;
end intrinsic; 

// TODO: narrow>1
intrinsic CuspFormBasis(M::ModFrmHilD, N::RngOrdIdl, k::SeqEnum[RngIntElt]) -> SeqEnum[ModFrmHilDElt], RngIntElt 
   {returns a basis for M of weight k}  
   basis := []; 
   newforms_dimension := 0; 
   //TODO should we sieve? 
   for dd in Divisors(N) do 
     basis := []; 
     orbit_representatives := NewformsToHMF(M, dd, k); 
     orbits := [GaloisOrbitDescent(elt) : elt in orbit_representatives]; // this is a sequence of sequences of HMFs
     OldSpace := [];
     for orbit in orbits do
       OldSpace := &cat[Inclusion(elt,N) : elt in orbit]; 
     end for;
     if dd eq N then 
       if #orbits eq 0 then 
         newforms_dimension := 0; 
       else 
        newforms_dimension := &+[ #orbit : orbit in orbits];
       end if; 
     end if; 
     basis cat:= OldSpace;
  end for; 
  return basis, newforms_dimension; 
end intrinsic; 


intrinsic Basis(M::ModFrmHilD, N::RngOrdIdl, k::SeqEnum[RngIntElt]) -> SeqEnum[ModFrmHilDElt], RngIntElt 
    { returns a Basis for the space } 
    // Cuspforms
    CB, newforms_dimension := CuspFormBasis(M, N, k);
    //Eisenstein Series
    ZF := Integers(M);
    n := Degree(ZF);
    B := CB;
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
   						B cat:= [E];
   					end if;
   				else
   					if Set([Component(H_psi,i) eq Component(H_eta,i) : i in [1..n]]) eq {false} then
   						E := EisensteinSeries(M, N, eta, psi, k);
   						B cat:= [E];
   					end if;
   				end if;
   			end for;
   		end for;
   	end for;
   return B, newforms_dimension; 
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
