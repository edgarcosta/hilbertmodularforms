procedure ExtendMultiplicativelyHelper(~coeffs, ~mfh_reps, M, N, k, chi, FourierCoeffMode)
  prime_ideals := PrimeIdeals(M);
  ideals := Ideals(M);
  factorization := func<nn | Factorization(M, nn)>;
  
  // Initialize
  ZF := Order(N);
  F := NumberField(ZF);
  
  // Determine the type of coefficients by checking an existing coefficient
  // When called from Newforms.m with GaloisDescent, coefficients are always matrices (Hecke operators)
  // When called from CuspEigenformFromCoeffsAtPrimes, coefficients are scalars (eigenvalues)
  is_matrix_mode := exists(nn){nn : nn in Keys(coeffs) | Type(coeffs[nn]) eq AlgMatElt};
  
  if is_matrix_mode then
    // Matrix mode: Get dimensions from an existing coefficient
    sample_coeff := coeffs[Rep({pp : pp in prime_ideals | IsDefined(coeffs, pp)})];
    n := Nrows(sample_coeff);
    R := BaseRing(sample_coeff);
    coeffs[0*ZF] := ZeroMatrix(R, n, n);
    coeffs[1*ZF] := IdentityMatrix(R, n);
  else
    // Scalar mode: Use scalar values
    coeffs[0*ZF] := 0;
    coeffs[1*ZF] := 1;
  end if;
  
  if FourierCoeffMode then
    mfh_reps[0*ZF] := 0;
    mfh_reps[1*ZF] := 1;
  end if;

  // set recursion for p^e
  max_norm := Norm(ideals[#ideals]);
  prec := Floor(Log(2, max_norm)) + 1;
  Q := Rationals();
  QX<X, Y> := PolynomialRing(Q, 2);
  R<T> := PowerSeriesRing(QX : Precision := prec);
  recursion := Coefficients(1/(1 - X*T + Y*T^2));
  
  vprintf HilbertModularForms: "ExtendMultiplicatively: Computing coefficients of p^e...\n";
  t0 := Cputime();
  
  for pp in prime_ideals do
    // Compute the second recursion parameter (Y in the power series)
    if N subset pp then
      y := 0;
    else
      if FourierCoeffMode then
        // Nonparitious: use pi^(k-1) where pi is the totally positive generator
        pi := mfh_reps[pp];
        assert IsTotallyPositive(pi);
        auts := AutsOfKReppingEmbeddingsOfF(F, F);
        y := chi(pp) * &*[auts[i](pi)^(k[i] - 1) : i in [1 .. #k]];
      else
        // Paritious: use Norm(pp)^(k0-1)
        k0 := Max(k);
        y := chi(pp) * Norm(pp)^(k0 - 1);
      end if;
    end if;
    
    // Compute coefficients for prime powers p^e
    ppe := pp;
    for e in [2..Floor(Log(Norm(pp), max_norm))] do
      ppe *:= pp;
      coeffs[ppe] := Evaluate(recursion[e+1], [coeffs[pp], y]);
      if FourierCoeffMode then
        mfh_reps[ppe] := mfh_reps[pp]^e;
      end if;
    end for;
  end for;
  
  vprintf HilbertModularForms: "  Time for p^e coefficients: %.3o seconds\n", Cputime() - t0;
  
  vprintf HilbertModularForms: "ExtendMultiplicatively: Computing coefficients of general n...\n";
  t1 := Cputime();
  
  // Build a map from ideals to their exponent vectors
  // Each ideal nn = prod_i p_i^{e_i} is represented as a tuple (e_1, ..., e_r)
  ideal_to_exponents := AssociativeArray();
  exponents_to_ideal := AssociativeArray();
  
  for nn in ideals do
    if nn eq 0*ZF then
      continue;
    end if;
    fac := factorization(nn);
    exps := [0 : _ in prime_ideals];
    for pair in fac do
      pp := pair[1];
      e := pair[2];
      idx := Index(prime_ideals, pp);
      if idx ne 0 then
        exps[idx] := e;
      end if;
    end for;
    exp_tuple := <exps[i] : i in [1..#exps]>;
    ideal_to_exponents[nn] := exp_tuple;
    exponents_to_ideal[exp_tuple] := nn;
  end for;
  
  // Sort ideals by L1 norm of their exponent vectors
  // This ensures that when we compute a_nn, we've already computed all necessary factors
  ideal_list := [nn : nn in ideals | nn ne 0*ZF and not IsDefined(coeffs, nn)];
  l1_norms := [&+[e : e in ideal_to_exponents[nn]] : nn in ideal_list];
  ParallelSort(~l1_norms, ~ideal_list);
  
  // Extend multiplicatively: for each ideal, compute using one multiplication
  for nn in ideal_list do
    exp_vec := ideal_to_exponents[nn];
    
    // Find the first nonzero exponent
    j := 0;
    for i in [1..#exp_vec] do
      if exp_vec[i] ne 0 then
        j := i;
        break;
      end if;
    end for;
    
    if j eq 0 then
      // This is the unit ideal, should already be defined
      continue;
    end if;
    
    // Compute nn = p_j^{e_j} * (nn / p_j^{e_j})
    pp := prime_ideals[j];
    ppe := pp^exp_vec[j];
    nn_reduced := nn / ppe;
    
    // Compute a_nn = a_{p_j^{e_j}} * a_{nn / p_j^{e_j}}
    if is_matrix_mode then
      coeffs[nn] := coeffs[ppe] * coeffs[nn_reduced];
    else
      coeffs[nn] := StrongMultiply([* coeffs[ppe], coeffs[nn_reduced] *]);
    end if;
    
    if FourierCoeffMode then
      mfh_reps[nn] := mfh_reps[ppe] * mfh_reps[nn_reduced];
    end if;
  end for;
  
  vprintf HilbertModularForms: "  Time for general n coefficients: %.3o seconds\n", Cputime() - t1;
end procedure;

// Generic extending multiplicatively (paritious case only)
intrinsic ExtendMultiplicatively(
    ~coeffs::Assoc, 
    Mk::ModFrmHilD
    )
  { 
    Extends coefficients multiplicatively from prime powers to all ideals (paritious case).
    
    Inputs:
      coeffs - associative array to be filled with coefficients
      Mk - space of Hilbert modular forms
  }
  
  dummy_reps := AssociativeArray();
  ExtendMultiplicativelyHelper(~coeffs, ~dummy_reps, Parent(Mk), Level(Mk), Weight(Mk), Character(Mk), false);
end intrinsic;

// Generic extending multiplicatively (nonparitious case with Fourier coefficients)
intrinsic ExtendMultiplicatively(
    ~coeffs::Assoc,
    ~mfh_reps::Assoc,
    Mk::ModFrmHilD
    )
  { 
    Extends coefficients multiplicatively from prime powers to all ideals (nonparitious case).
    Also tracks totally positive generators in mfh_reps.
    
    Inputs:
      coeffs - associative array to be filled with coefficients
      mfh_reps - associative array to be filled with totally positive generators
      Mk - space of Hilbert modular forms
  }
  
  ExtendMultiplicativelyHelper(~coeffs, ~mfh_reps, Parent(Mk), Level(Mk), Weight(Mk), Character(Mk), true);
end intrinsic;
 
function codifferent_generator(M)
  // input
  //   M::GradedRingOfHMFs - A graded ring of HMFs over a field F with h+(F) = 1
  // returns
  //   A canonical totally positive generator for the codifferent.
  if not assigned M`CodifferentGenerator then
    F := BaseField(M);
    ZF := Integers(F);
    assert NarrowClassNumber(F) eq 1;
    _, d_inv := IsNarrowlyPrincipal(Different(ZF)^-1);
    M`CodifferentGenerator, _ := FunDomainRep(M, d_inv);
  end if;
  return M`CodifferentGenerator;
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
    nup := codifferent_generator(Parent(Mk)) * mfh_nn;
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
  prime_ideals := PrimeIdeals(M);
  ideals := Ideals(M);

  // get coefficients at every nn, not just the prime ideals
  if from_a_pp then
    ExtendMultiplicatively(~coeffs_by_nn, Mk);
  else
    assert mfh_reps cmpne 0;
    ExtendMultiplicatively(~coeffs_by_nn, ~mfh_reps, Mk);
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

