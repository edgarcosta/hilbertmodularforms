////////// Creation of CuspForms from ModFrmHilDElt //////////
// Todo: Edgar originally had a clever setup that completely advoided factoring ideals for the recursion. However this assumed that the ideals were ordered by norm which has been switched.




intrinsic CoefficientsFromRecursion(M::ModFrmHilD, N::RngOrdIdl, n::RngOrdIdl, k::SeqEnum[RngIntElt], coeff::Assoc) -> RngIntElt
  {construct the coefficient for a_n from an associative array coeff with all a_p for p|n}
  ZF := Integers(M);
  k0 := Max(k); 
  Fact := Factorization(n);
  // Power series ring for recusion
  ZFX<X, Y> := PolynomialRing(ZF, 2);
  prec := Max([pair[2]: pair in Fact]) +1;
  R<T> := PowerSeriesRing(ZFX : Precision := prec);
  recursion := Coefficients(1/(1 - X*T + Y*T^2));
  // If good, then 1/(1 - a_p T + Norm(p) T^2) = 1 + a_p T + a_{p^2} T^2 + ...
  // If bad, then 1/(1 - a_p T) = 1 + a_p T + a_{p^2} T^2 + ...
  coeff_I := 1;
  for pair in Fact do 
    pp := pair[1];
    Np := Norm(pp)^(k0-1);
    // if pp is bad
    if N subset pp then
      Np := 0;
    end if;
    coeff_I *:= Evaluate(recursion[pair[2]], [coeff[pp], Np]);
  end for;
  return coeff_I;
end intrinsic;

intrinsic NewformToHMF(M::ModFrmHilD, N::RngOrdIdl, k::SeqEnum[RngIntElt], newform::ModFrmHilElt) -> ModFrmHilDElt
  {Construct the ModFrmHilDElt in M determined (on prime ideals up to norm prec) by hecke_eigenvalues.}
  ZF := Integers(M);
  // Coefficient array indexed by ideals
  coeffs := AssociativeArray(); 

  // Step 1: a_0 and a_1
  coeffs[0*ZF] := 0; coeffs[1*ZF] := 1;
  // Step 2: a_p for primes 
  for pp in AllPrimes(M) 
    do coeffs[pp] := HeckeEigenvalue(newform, pp);
  end for;
  // Step 3: a_n for composite ideals
  for I in AllIdeals(M) do 
    if I notin Keys(coeffs) then 
      coeffs[I] := CoefficientsFromRecursion(M,N,I,k,coeffs);
    end if;
  end for;

  //Sorting the ideals into a new array indexed by Cl^+(K)
  CoeffsArray := AssociativeArray();
  bbs := NarrowClassGroupReps(M);
  for bb in bbs do
    CoeffsArray[bb] := AssociativeArray();
    for nn in IdealsByNarrowClassGroup(M)[bb] do
      CoeffsArray[bb][nn] := coeffs[nn];
    end for;
  end for;
  return HMF(M, N, k, CoeffsArray);
end intrinsic;


// Edgar original function. ///

/* intrinsic EigenformToHMF(M::ModFrmHilD, N::RngOrdIdl, k::SeqEnum[RngIntElt], hecke_eigenvalues::Assoc) -> ModFrmHilDElt */
/*   {Construct the ModFrmHilDElt in M determined (on prime ideals up to norm prec) by hecke_eigenvalues.} */
/*   // pull info from M */
/*   F := BaseField(M); */
/*   prec := Precision(M); */
/*   // a prime */
/*   pp := Random(Keys(hecke_eigenvalues)); */
/*   // assertions */
/*   if not Set(PrimesUpTo(prec, F)) subset Keys(hecke_eigenvalues) then */
/*     print "Not enough primes"; */
/*     assert false; */
/*   end if; */
/*   k0 := Max(k); */
/*   // power series ring */
/*   log_prec := Floor(Log(prec)/Log(2)); // prec < 2^(log_prec+1) */
/*   ZK := Parent(hecke_eigenvalues[pp]); */
/*   ZKX<X, Y> := PolynomialRing(ZK, 2); */
/*   R<T> := PowerSeriesRing(ZKX : Precision := log_prec + 1); */
/*   // If good, then 1/(1 - a_p T + Norm(p) T^2) = 1 + a_p T + a_{p^2} T^2 + ... */
/*   // If bad, then 1/(1 - a_p T) = 1 + a_p T + a_{p^2} T^2 + ... */
/*   recursion := Coefficients(1/(1 - X*T + Y*T^2)); */
/*   ideals := Ideals(M); */
/*   coeffs := [ZK!0: i in ideals]; */
/*   set := [false : c in coeffs]; */
/*   coeffs[1] := 0; //a_0 */
/*   coeffs[2] := 1; //a_1 */
/*   set[1] := true; */
/*   set[2] := true; */
/*   dict := Dictionary(M); */
/*   for i := 1 to #coeffs do */
/*     if not set[i] then */
/*       // is[i] is a prime */
/*       pp := ideals[i]; */
/*       assert IsPrime(pp); */
/*       coeffs[i] := hecke_eigenvalues[pp]; */
/*       set[i] := true; */
/*       Np := Norm(pp)^(k0-1); */
/*       // if pp is bad */
/*       if N subset pp then */
/*         Np := 0; */
/*       end if; */
/*       r := 2; */
/*       pp_power := pp * pp; */
/*       //deals with powers of p */
/*       while pp_power in Keys(dict) do */
/*         ipower := dict[pp_power]; */
/*         coeffs[ipower] := Evaluate(recursion[r + 1], [coeffs[i], Np]); */
/*         set[ipower] := true; */
/*         pp_power *:= pp; */
/*         r +:= 1; */
/*       end while; */
/*       //deal with multiples of its powers by smaller numbers */
/*       for j := 3 to #coeffs do */
/*         if set[j] and not (ideals[j] subset pp) then */
/*           mm := ideals[j]; */
/*           pp_power := pp; */
/*           mmpp_power := mm * pp_power; */
/*           while mmpp_power in Keys(dict) do */
/*             l := dict[mmpp_power]; */
/*             assert set[l] eq false; */
/*             ipower := dict[pp_power]; */
/*             // a_{m * pp_power} := a_{m} * a_{pp_power} */
/*             coeffs[l] := coeffs[j] * coeffs[ipower]; */
/*             set[l] := true; */
/*             mmpp_power *:= pp; */
/*             pp_power *:= pp; */
/*           end while; */
/*         end if; //check if it's set */
/*       end for; //loop in j */
/*     end if; // check if it's set */
/*   end for; // loop in i */
/*   for i := 1 to #coeffs do */
/*     assert set[i]; */
/*   end for; */
/*   return HMF(M, N, k, coeffs); */
/* end intrinsic; */



intrinsic NewformsToHMF(M::ModFrmHilD, N::RngOrdIdl, k::SeqEnum[RngIntElt]) -> SeqEnum[ModFrmHilDElt]
  {returns Hilbert newforms} 
  F := BaseField(M); 
  prec := Precision(M); 
  MF := HilbertCuspForms(F, N, k); 
  S := NewSubspace(MF); 
  newspaces  := NewformDecomposition(S); 
  newforms := [* Eigenform(U) : U in newspaces *]; 
  HMFnewforms := [**]; 
  for newform in newforms do
    NewHMF := NewformToHMF(M, N, k, newform);
    Append(~HMFnewforms, NewHMF); 
  end for; 
  return HMFnewforms;
end intrinsic; 

/*
intrinsic NewformsToHMF2(M::ModFrmHilD, k::SeqEnum[RngIntElt]) -> SeqEnum[ModFrmHilDElt]
  {returns Hilbert newforms}
  F := BaseField(M);
  N := Level(M); //input
  prec := Precision(M);
  HeckeEigenvalue := HeckeEigenvalues(M);
  key :=  [* N, k *];
  if not IsDefined(M, key) then
    MF := HilbertCuspForms(F, N, k);
    S := NewSubspace(MF);
    newspaces  := NewformDecomposition(S);
    newforms := [* Eigenform(U) : U in newspaces *];
    primes := Primes(M);
    EVnewforms := [];
    for newform in newforms do
      eigenvalues := [];
      for i in [1..#primes] do
          eigenvalues[i] := HeckeEigenvalue(newform, primes[i]);
      end for;
      Append(~EVnewforms, eigenvalues);
    end for;
    HeckeEigenvalue[key] := EVnewforms;
  else
    EVnewforms := HeckeEigenvalue[key];
  end if;
  HMFnewforms := [];
  for eigenvalues in EVnewforms do
      ef := EigenformToHMF(M, k, eigenvalues); //FIXME, this is not correct
      Append(~HMFnewforms, ef);
    end for;
  return HMFnewforms;
end intrinsic;
*/

// TODO: narrow>1
/* intrinsic CuspFormBasis(M::ModFrmHilD, N::RngOrdIdl, k::SeqEnum[RngIntElt]) -> SeqEnum[ModFrmHilDElt], RngIntElt */
/*   {returns a basis for M of weight k} */
/*   prec := Precision(M); */
/*   F := BaseField(M); */
/*   ideals := Ideals(M); */
/*   dict := Dictionary(M); */
/*   set_ideals := Keys(dict); */
/*   zero_coeffs := [0 : i in [1..#ideals]]; */
/*   basis := []; */
/*   newforms_dimension := 0; */
/*   //TODO should we sieve? */
/*   for dd in Divisors(N) do */
/*     basis := []; */
/*     orbit_representatives := NewformsToHMF(M, N, k); */
/*     orbits := [GaloisOrbitDescent(elt) : elt in orbit_representatives]; */
/*     old_space_basis := &cat orbits; */
/*     old_space_coeffs := [Coefficients(elt) : elt in old_space_basis]; */
/*     for ee in Divisors(N/dd) do */
/*       new_coeffs_ee := [ zero_coeffs : i in [1..#old_space_basis]]; */
/*       for i := 1 to #ideals do */
/*         Iee := ideals[i]*ee; */
/*         if Iee in set_ideals then */
/*           Iee_cord := dict[Iee]; */
/*           for j := 1 to #old_space_basis do */
/*             new_coeffs_ee[j][Iee_cord] := old_space_coeffs[j][i]; */
/*           end for; */
/*         else */
/*           //this assumes ideals are sorted by norm!! */
/*           break i; */
/*         end if; */
/*       end for; */
/*       basis := basis cat [HMF(M, N, k, elt) : elt in new_coeffs_ee]; */
/*     end for; */
/*     if dd eq N then */
/*       if #orbits eq 0 then */
/*         newforms_dimension := 0; */
/*       else */
/*         newforms_dimension := &+[ #orbit : orbit in orbits]; */
/*       end if; */
/*     end if; */
/*   end for; */
/*   return basis, newforms_dimension; */
/* end intrinsic; */
