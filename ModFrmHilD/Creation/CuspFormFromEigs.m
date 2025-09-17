// Generic extending multiplicatevely
intrinsic ExtendMultiplicatively(~coeffs::Assoc, N::RngOrdIdl, k::SeqEnum[RngIntElt], chi::., prime_ideals::SeqEnum, ideals::SeqEnum[RngOrdIdl] : factorization:=false)
  { set a_nn := prod(a_p^e : (p,e) in factorization(nn) }
  // TODO: take character into acount
  
  // We don't worry about putting things in the right coefficient field at this point
  // TODO abhijitm there's probably a cleaner way to get 
  // the zero ideal and unit ideal...
  coeffs[0*N] := 0;
  coeffs[N*N^-1] := 1;

  k0 := Max(k);
  if factorization cmpeq false then
    factorization := Factorization;
  end if;

  // set recursion
  // ideals must be sorted by Norm
  max_norm := Norm(ideals[#ideals]);
  prec := Floor(Log(2, max_norm)) + 1;
  Q := Rationals();
  // Power series ring for recursion
  QX<X, Y> := PolynomialRing(Q, 2);
  R<T> := PowerSeriesRing(QX : Precision := prec);
  recursion := Coefficients(1/(1 - X*T + Y*T^2));
  // If good, then 1/(1 - a_p T + Chi(p)*Norm(p)^{k0-1} T^2) = 1 + a_p T + a_{p^2} T^2 + ...
  // If bad, then 1/(1 - a_p T) = 1 + a_p T + a_{p^2} T^2 + ...
  for p in prime_ideals do
    Np := Norm(p);
    if N subset p then
      Npk := 0;
    else
      Npk := Np^(k0 - 1);
    end if;
    pe := p;
    Npe := Np;
    for e in [2..Floor(Log(Norm(p), max_norm))] do
      pe *:= p; // p**e
      Npe *:= Np;
      // pe might not be in ideals, but still might show up as a factor
      if Npe gt max_norm then
        break;
      end if;
      coeffs[pe] := Evaluate(recursion[e+1], [coeffs[p], Npk * chi(p)]);
    end for;
  end for;
  // extend multiplicatively
  for n in ideals do
    if not IsDefined(coeffs, n) then
      coeffs[n] := StrongMultiply([* coeffs[pair[1]^pair[2]] : pair in factorization(n) *]);
    end if;
  end for;
end intrinsic;

// TODO abhijitm remove code reuse by combining this and the above? 
// Also, the output of this function is strange because it's keyed by ideal
// but stores Fourier coefficients. It makes sense in context of the current
// Creation/Newforms.m code but it seems like there should be a cleaner way.
intrinsic ExtendMultiplicativelyFourier(
    ~coeffs::Assoc,
    ~mfh_reps::Assoc,
    Mk::ModFrmHilD
    )
  {}
  F := BaseField(Mk);
  ZF := Integers(F);
  N := Level(Mk);
  k := Weight(Mk);
  chi := Character(Mk);
  prime_ideals := PrimeIdeals(Parent(Mk));
  ideals := Ideals(Parent(Mk));

  coeffs[0*ZF] := 0;
  coeffs[1*ZF] := 1;
  mfh_reps[0*ZF] := 0;
  mfh_reps[1*ZF] := 1;

  // set recursion
  // ideals must be sorted by Norm
  max_norm := Norm(ideals[#ideals]);
  prec := Floor(Log(2, max_norm)) + 1;
  Q := Rationals();
  // Power series ring for recursion
  QX<X, Y> := PolynomialRing(Q, 2);
  R<T> := PowerSeriesRing(QX : Precision := prec);
  recursion := Coefficients(1/(1 - X*T + Y*T^2));
  // If good, then 1/(1 - a_p T + Chi(p)*Norm(p)^{k0-1} T^2) = 1 + a_p T + a_{p^2} T^2 + ...
  // If bad, then 1/(1 - a_p T) = 1 + a_p T + a_{p^2} T^2 + ...
  for pp in prime_ideals do
    // a totally positive element of F generating the ideal pp
    pi := mfh_reps[pp];
    if N subset pp then
      z := 0;
    else
      auts := AutsOfKReppingEmbeddingsOfF(F, F);
      z := &*[auts[i](pi)^(k[i] - 1) : i in [1 .. #k]];
    end if;

    assert IsTotallyPositive(pi);
    ppe := pp; // will store p^e in the eth iteration
    for e in [2..Floor(Log(Norm(pp), max_norm))] do
      ppe *:= pp;
      coeffs[ppe] := Evaluate(recursion[e+1], [coeffs[pp], chi(pp) * z]);  
      mfh_reps[ppe] := pi^e;
    end for;
  end for;

  for nn in ideals do
    if IsZero(nn) or IsOne(nn) then
      continue;
    end if;
    
    // list of things to be multiplied
    mult_list := [* *];
    // The product of mfh_reps corresponding to the factorization of N.
    // This will differ from nu (the rep associated to the ideal nn by
    // IdealToRep(M, nn)) by a totally positive unit
    // 
    // We start with a generator of the (co)different because nu = dd^-1 * nn
    mfh_nn := F!1;
    for pair in Factorization(nn) do
      Append(~mult_list, coeffs[pair[1]^pair[2]]);
      mfh_nn *:= mfh_reps[pair[1]]^pair[2];
    end for;
    coeffs[nn] := StrongMultiply(mult_list);
    mfh_reps[nn] := mfh_nn;
  end for;
end intrinsic;
 
function dinv(M)
  // input
  //   M::GradedRingOfHMFs - A graded ring of HMFs over a field F with h+(F) = 1
  // returns
  //   A canonical totally positive generator for the codifferent.
  F := BaseField(M);
  ZF := Integers(F);
  assert NarrowClassNumber(F) eq 1;
  _, d_inv := IsNarrowlyPrincipal(Different(ZF)^-1);
  d_inv, _ := FunDomainRep(M, d_inv);
  return d_inv;
end function;

// TODO abhijitm this should disappear once the Newforms logic is rewritten
function coeff_from_ext_mult_fourier(Mk, coeff_nn, mfh_nn, nn : bb:=1*Integers(BaseField(Mk)))
  /******************
   *  inputs:
   *    Mk::ModFrmHilD
   *    coeff_nn::FldNumElt - The coefficient stored in coeffs[nn] in the Newforms code. It is 
   *      the eigenvalue of some Hecke operator T_n for n a totally positive generator of nn
   *      (this will be the same as the usual T_nn up to a constant).
   *    mfh_nn::FldNumElt - The value n above
   *    nn::RngOrdIdl - The ideal 
   *    bb::RngOrdIdl - A narrow class group rep. This is nonfunctional for now as we currently 
   *      require that the narrow class number be 1 anyways.
   *  returns:
   *    The coefficient a_nu where nu is the fundamental domain rep corresponding to the ideal
   *    nn. It is equal to coeff_nn up to some unit character.
   **********************/
  if IsZero(mfh_nn) then
    return coeff_nn * 0;
  else
    nup := dinv(Parent(Mk)) * mfh_nn;
    nu := IdealToRep(Parent(Mk), nn);
    eps := nu / nup;
    uc := Mk`UnitCharacters[bb];
    return coeff_nn * Evaluate(uc, eps);
  end if;
end function;

intrinsic CuspEigenformFromCoeffsAtPrimes(
    Mk::ModFrmHilD,
    coeffs_by_nn::Assoc :
    coeff_ring:=DefaultCoefficientRing(Mk),
    from_a_pp:=true,
    mfh_reps:=0
    ) -> ModFrmHilDElt
  {
    inputs:
      Mk - Space of HMFs
      coeffs_by_nn - Poorly named, but this is an associative array
        indexed by prime ideals pp up to Precision(Parent(Mk)). 
        If from_a_pp is true then coeffs_by_nn[pp] stores the coefficient a_pp.
        If from_a_pp is false then coeffs_by_nn[pp] stores the tuple <pi, a_pi>,
        where pi is a totally positive generator of pp (we assume that the narrow
        class number of the field is 1) and a_pi is the Fourier coefficient at pi
      coeff_ring - Coefficient ring of these cusp forms. This is the field of
        a_pp when from_a_pp is true and the field of the a_pi when from_a_pp is false.
    returns:
      The cusp form with these Hecke eigenvalues
  }
  M := Parent(Mk);
  F := BaseField(Mk);

  // get coefficients at every nn, not just the prime ideals
  if from_a_pp then
    ExtendMultiplicatively(
      ~coeffs_by_nn,
      Level(Mk),
      Weight(Mk),
      Character(Mk),
      PrimeIdeals(M),
      Ideals(M) :
      factorization:=func<n|Factorization(M, n)>
      );
  else
    assert mfh_reps cmpne 0;
    ExtendMultiplicativelyFourier(~coeffs_by_nn, ~mfh_reps, Mk);
  end if;

  // TODO abhijitm once Jean's improvements are in, this construction
  // should be rewritten
  coeffs_by_nu := AssociativeArray();
  
  for bb in NarrowClassGroupReps(M) do
    coeffs_by_nu[bb] := AssociativeArray();
    coeffs_by_nu[bb][F!0] := coeff_ring!0;
  end for;

  ideals := Exclude(Ideals(M), ideal<Integers(F) | 0>);

  for nn in ideals do
    bb := IdealToNarrowClassRep(M, nn);
    nu := IdealToRep(M)[bb][nn];
    if from_a_pp then
      a_nn := coeffs_by_nn[nn];
      coeffs_by_nu[bb][nu] := IdlCoeffToEltCoeff(a_nn, nu, Weight(Mk), coeff_ring);
    else
      // nup is a totally positive generator of nn, but won't typically be the 
      // fundamental representative nu corresponding to nn
      a_nup := coeffs_by_nn[nn];
      nup := mfh_reps[nn];
      // recover a_nu from a_nup and store it in coeffs_by_nu[bb][nu]
      coeffs_by_nu[bb][nu] := coeff_from_ext_mult_fourier(Mk, a_nup, nup, nn);
    end if;
  end for;

  return HMF(Mk, coeffs_by_nu : coeff_ring := coeff_ring);
end intrinsic;

