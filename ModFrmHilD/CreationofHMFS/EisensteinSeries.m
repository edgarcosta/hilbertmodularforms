// TODO: narrow>1
// TODO needs testing
/* intrinsic EisensteinSeries(M::ModFrmHilD, N::RngOrdIdl, eta::GrpHeckeElt, psi::GrpHeckeElt, k::SeqEnum[RngIntElt]) -> ModFrmHilDElt */
/*   {Let aa*bb be the modulus of psi*eta^-1. Return the Eisenstein series E_k(eta,psi) in M_k(aa*bb,eta*psi).} */
/*   Cl := NarrowClassGroup(M); */
/*   mp := NarrowClassGroupMap(M); */
/*   X := Parent(eta); */
/*   assert X eq Parent(psi); */
/*   K := X`TargetRing; // where the character values live */
/*   if #Cl eq 1 then */
/*     tt := mp(Cl.0); */
/*   else */
/*     error "not implemented for narrow class number > 1."; */
/*   end if; */
/*   n := Degree(BaseField(M)); */
/*   assert #SequenceToSet(k) eq 1; // only parallel weight for now */
/*   nn := N; */
/*   // aa := Conductor(eta); */
/*   aa := Modulus(eta); */
/*   // bb := Conductor(psi); */
/*   bb := Modulus(psi); */
/*   assert nn subset aa; */
/*   assert nn subset bb; */
/*   Haa := HeckeCharacterGroup(aa); */
/*   Hbb := HeckeCharacterGroup(bb); */
/*   ideals := Ideals(M); */
/*   coeffs := [ K!0 : i in [1..#ideals]]; */
/*   if k[1] ge 2 then */
/*     // constant term */
/*     if aa eq ideal<Order(aa)|1> then */
/*       prim := AssociatedPrimitiveCharacter(psi*eta^(-1)); */
/*       coeffs[1] := 2^(-n)*(eta^(-1))(tt)*LValue_Recognized(M, N, prim, k); */
/*     else */
/*       coeffs[1] := 0; */
/*     end if; */
/*   elif k[1] eq 1 then // wt 1 case */
/*     if aa eq ideal<Order(aa)|1> and bb ne ideal<Order(bb)|1> then */
/*       prim := AssociatedPrimitiveCharacter(psi*eta^(-1)); */
/*       coeffs[1] := 2^(-n)*(eta^(-1))(tt)*LValue_Recognized(M, N, prim, k); */
/*     elif aa ne ideal<Order(aa)|1> and bb eq ideal<Order(bb)|1> then */
/*       prim := AssociatedPrimitiveCharacter(psi^(-1)*eta); */
/*       coeffs[1] := 2^(-n)*(psi^(-1))(tt)*LValue_Recognized(M, N, prim, k); */
/*     elif aa eq ideal<Order(aa)|1> and bb eq ideal<Order(bb)|1> then */
/*       prim1 := AssociatedPrimitiveCharacter(psi*eta^(-1)); */
/*       prim2 := AssociatedPrimitiveCharacter(psi^(-1)*eta); */
/*       coeffs[1] := 2^(-n)*((eta^(-1))(tt)*LValue_Recognized(M, N, prim1, k) */
/*                           +(psi^(-1))(tt)*LValue_Recognized(M, N, prim2, k)); */
/*     elif aa ne ideal<Order(aa)|1> and bb ne ideal<Order(bb)|1> then */
/*       coeffs[1] := 0; */
/*     end if; */
/*   else // nonpositive and half-integral weights... */
/*     error "Not implemented"; */
/*   end if; */
/*   // other terms */
/*   for i := 2 to #ideals do // 2 here assumes #Cl = 1 FIXME */
/*     mm := ideals[i]; */
/*     sum := 0; */
/*     for rr in Divisors(mm) do */
/*       sum +:= eta(mm/rr)*psi(rr)*Norm(rr^(k[1]-1)); */
/*     end for; */
/*     coeffs[i] := sum; */
/*   end for; */
/*   if not (coeffs[1] in [0,1]) then */
/*     factor := 1/coeffs[1]; */
/*     coeffs := [factor * elt : elt in coeffs]; */
/*   end if; */
/*   if IsIsomorphic(K, RationalsAsNumberField()) then */
/*     coeffs := [ Rationals() ! elt : elt in coeffs ]; */
/*   end if; */
/*   return HMF(M, N, k, coeffs); */
/* end intrinsic; */

// TODO finish this and use in EisensteinSeries intrinsic

//Toolbox function to use in the Eisenstein series function--gives us an L value
/* intrinsic LValue_Recognized(M::ModFrmHilD, N::RngOrdIdl, prim::GrpHeckeElt, k::SeqEnum[RngIntElt]) -> FldNumElt */
/*   {This is a toolbox function to compute L values in the right space} */
/*   // Lf := LSeries(prim : Precision := 50); */
/*   // TODO clean up precision */
/*   // Maybe a separate function to compute L-values? */
/*   K := Parent(prim)`TargetRing; // where the character values live */
/*   Lf := LSeries(prim : Precision := 100); */
/*   LSetPrecision(Lf, 100); // do we need this? */
/*   Lvalue := Evaluate(Lf, 1-k[1]); */
/*   // figure out the right place */
/*   primes := PrimesUpTo(Precision(M), BaseField(M)); */
/*   places := InfinitePlaces(K); */
/*   i := 1; */
/*   while #places gt 1 and i le #primes do */
/*     pp := primes[i]; */
/*     app := prim(pp); */
/*     places := [pl : pl in places | Evaluate(app, pl) eq -Coefficients(EulerFactor(Lf, pp : Degree := 1))[2] ]; */
/*     // why is this the right way to find the correct place to recognize? */
/*     i +:=1; */
/*   end while; */
/*   assert #places eq 1; */
/*   pl := places[1]; */
/*   CC<I> := ComplexField(Precision(Lvalue)); */
/*   return RecognizeOverK(CC!Lvalue, K, pl, false); */
/* end intrinsic; */
