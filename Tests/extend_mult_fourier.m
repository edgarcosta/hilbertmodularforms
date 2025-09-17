import "ModFrmHilD/Creation/CuspFormFromEigs.m" : coeff_from_ext_mult_fourier;

procedure test(Mk, bb)
  F := BaseField(Mk);
  k := Weight(Mk);
  ZF := Integers(F);
  M := Parent(Mk);
  prec := Precision(M);
  uc := Mk`UnitCharacters[bb];

  Sk := CuspFormBasis(Mk);
  if #Sk eq 1 then
    f := Sk[1];
  else
    Ek := Eigenbasis(Mk, Sk : P:=10, coprime_only:=false);
  end if;

  f := DivideByFirstNonzeroIdlCoeff(f);
  coeffs := AssociativeArray();
  mfh_reps := AssociativeArray();
  U, mU := TotallyPositiveUnitsGroup(F);

  // choosing d is essentially choosing which of the Fourier
  // coefficients associated to nn = (1) we are normalizing to be 1
  _, dinv := IsNarrowlyPrincipal(Different(ZF)^-1);
  dinv, _ := FunDomainRep(M, dinv);

  primes := PrimesUpTo(prec, F);
  for pp in primes do
    nu := IdealToRep(M, pp);
    pi := nu * dinv^-1; // (nu) = pp * dd^-1 so (pi * d) = nu
    assert Norm(pi) eq Norm(pp);
    eps := mU(Random(U));
    pi_new := pi * eps;
    assert Coefficient(f, bb, nu) * Evaluate(uc, eps) eq Coefficient(f, bb, nu * eps);
    coeffs[pp] := Coefficient(f, bb, nu) * Evaluate(uc, eps) * EltToShiftedHalfWeight(dinv, k);
    mfh_reps[pp] := pi_new;
  end for;

  ExtendMultiplicativelyFourier(~coeffs, ~mfh_reps, Mk);

  coeffs_by_nu := AssociativeArray();
  coeffs_by_nu[bb] := AssociativeArray();
  for nu->nn in RepToIdeal(M)[bb] do
    if IsZero(nn) then
      coeffs_by_nu[bb][nu] := 0;
    else
      a_nup := coeffs[nn];
      a_nu := coeff_from_ext_mult_fourier(Mk, a_nup, mfh_reps[nn], nn);
      coeffs_by_nu[bb][nu] := a_nu;
    end if;
  end for;

  g := HMF(Mk, coeffs_by_nu);
  // they will not necessarily be the same because of the aforementioned normalization
  // choice resulting from our choice of d. 
  assert #LinearDependence([f, g]) eq 1;
end procedure;

/******  F = Q(sqrt(5)) ******/

F := QuadraticField(5);
ZF := Integers(F);
prec := 200;
M := GradedRingOfHMFs(F, prec);
bb := 1*ZF;


// parallel weight 2, coefficient field Q
N := Factorization(31*ZF)[1][1];
k := [2,2];
Mk := HMFSpace(M, N, k);
test(Mk, bb);


// weight [2,4], coefficient field F
N := Factorization(11*ZF)[1][1]; 
k := [2,4];
Mk := HMFSpace(M, N, k);
test(Mk, bb);

/******  F = Q(zeta7+) ******/


R<x> := PolynomialRing(Rationals());
F := NumberField(x^3-x^2-2*x+1);
ZF := Integers(F);
bb := 1*ZF;
M := GradedRingOfHMFs(F, prec);

// parallel weight 2
N := 3*ZF;
k := [2,2,2];
Mk := HMFSpace(M, N, k);
test(Mk, bb);

// weight [2,2,4]
N := 3*ZF;
k := [2,2,4];
Mk := HMFSpace(M, N, k);
test(Mk, bb);
