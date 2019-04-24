// TODO needs testing
// TODO fix normalization at the end
// Eisenstein Series have only been implemented for integral parallel weight 
intrinsic EisensteinSeries(M::ModFrmHilDGrRng, Sp::ModFrmHilD, eta::GrpHeckeElt, psi::GrpHeckeElt) -> ModFrmHilDElt 
  	{Let aa*bb be the modulus of psi*eta^-1. Return the Eisenstein series E_k(eta,psi) in M_k(aa*bb,eta*psi).} 
k := Weight(Sp);
N := Level(Sp);
  	Cl := NarrowClassGroup(M); 
   	mp := NarrowClassGroupMap(M); 
   	assert #SequenceToSet(k) eq 1; // Checking if parallel weight 

   	X := Parent(eta); 
   	assert X eq Parent(psi); 
   	CoefficientField := X`TargetRing; // where the character values live 
   		
   	n := Degree(BaseField(M));   	 
   	aa := Modulus(eta); // aa := Conductor(eta); 
   	bb := Modulus(psi); // bb := Conductor(psi);
   	assert N eq aa*bb;
   	Haa := HeckeCharacterGroup(aa); 
   	Hbb := HeckeCharacterGroup(bb); 

   	coeffs := AssociativeArray();
   	bbs := NarrowClassGroupReps(M);
   	ZF := Integers(M);
   	for tt in bbs do 
   		coeffs[tt] := AssociativeArray();
    	// a0 term for tt
   		// k > 1
    	if k[1] ge 2 then 
    		if aa eq 1*ZF then 
       			prim := AssociatedPrimitiveCharacter(psi*eta^(-1)); 
       			coeffs[tt][0*ZF] := 2^(-n)*(eta^(-1))(tt)*LValue_Recognized(M, N, prim, k); 
     		else 
       			coeffs[tt][0*ZF] := 0; 
     		end if; 
     	// k = 1
   		elif k[1] eq 1 then 
     	  if aa eq ideal<Order(aa)|1> and bb ne ideal<Order(bb)|1> then 
       		prim := AssociatedPrimitiveCharacter(psi*eta^(-1)); 
       		coeffs[1] := 2^(-n)*(eta^(-1))(tt)*LValue_Recognized(M, N, prim, k); 
     	  elif aa ne ideal<Order(aa)|1> and bb eq ideal<Order(bb)|1> then 
       		prim := AssociatedPrimitiveCharacter(psi^(-1)*eta); 
       		coeffs[1] := 2^(-n)*(psi^(-1))(tt)*LValue_Recognized(M, N, prim, k); 
     	  elif aa eq ideal<Order(aa)|1> and bb eq ideal<Order(bb)|1> then 
       		prim1 := AssociatedPrimitiveCharacter(psi*eta^(-1)); 
       		prim2 := AssociatedPrimitiveCharacter(psi^(-1)*eta); 
       		coeffs[1] := 2^(-n)*((eta^(-1))(tt)*LValue_Recognized(M, N, prim1, k) + (psi^(-1))(tt)*LValue_Recognized(M, N, prim2, k)); 
     	  elif aa ne ideal<Order(aa)|1> and bb ne ideal<Order(bb)|1> then 
       		coeffs[1] := 0; 
     	  end if;
      end if; 
   		// All other coefficients
   		for nn in IdealsByNarrowClassGroup(M)[tt] do 
        if nn ne 0*ZF then
    		  sum := 0; 
     		  for rr in Divisors(nn) do 
       			sum +:= eta(nn/rr)*psi(rr)*Norm(rr^(k[1]-1)); 
     		  end for; 
     		  coeffs[tt][nn] := sum; 
        end if;
   		end for; 
      // Makes coefficients rational
   		if IsIsomorphic(CoefficientField, RationalsAsNumberField()) then
        for nn in IdealsByNarrowClassGroup(M)[tt] do
    		  coeffs[tt][nn] := Rationals()!coeffs[tt][nn]; 
        end for;
      end if;
   	end for;
E := HMF(Sp, coeffs);
    // Normalized coefficients here. 
    if not (coeffs[bbs[1]][0*ZF] in [0,1]) then 
      E := (1/coeffs[bbs[1]][0*ZF]) * E;
    end if; 
   	return E;
 end intrinsic; 

// TODO finish this and use in EisensteinSeries intrinsic

//Toolbox function to use in the Eisenstein series function--gives us an L value
 intrinsic LValue_Recognized(M::ModFrmHilD, N::RngOrdIdl, prim::GrpHeckeElt, k::SeqEnum[RngIntElt]) -> FldNumElt 
   {This is a toolbox function to compute L values in the right space} 
   // Lf := LSeries(prim : Precision := 50); 
   // TODO clean up precision 
   // Maybe a separate function to compute L-values? 
   CoefficientField := Parent(prim)`TargetRing; // where the character values live 
   Lf := LSeries(prim : Precision := 100); 
   LSetPrecision(Lf, 100); // do we need this? 
   Lvalue := Evaluate(Lf, 1-k[1]); 
   // figure out the right place */
   primes := PrimesUpTo(Precision(M), BaseField(M)); 
   places := InfinitePlaces(CoefficientField); 
   i := 1; 
   while #places gt 1 and i le #primes do 
     pp := primes[i]; 
     app := prim(pp); 
     places := [pl : pl in places | Evaluate(app, pl) eq -Coefficients(EulerFactor(Lf, pp : Degree := 1))[2] ]; 
     // why is this the right way to find the correct place to recognize? */
     i +:=1; 
   end while; 
   assert #places eq 1; 
   pl := places[1]; 
   CC<I> := ComplexField(Precision(Lvalue)); 
   return RecognizeOverK(CC!Lvalue, CoefficientField, pl, false); 
 end intrinsic; 
