///////////////////////////////////////////////////
//                                               //
//                Hecke Operators                //
//                                               //
///////////////////////////////////////////////////

forward GetBasisForPrecisionIncrease;
forward ApplyBasisPrecisionIncrease;

///////////// ModFrmHilDElt: Hecke Operators ////////////////
intrinsic HeckeOperatorIdeal(f::ModFrmHilDElt, mm::RngOrdIdl : B:=false) -> ModFrmHilDElt
  {
    Returns T(mm)(f) for the character chi modulo the level of f.
    This function is designed for paritious forms and uses ideal coefficients.
    For nonparitious forms, use HeckeOperatorCoeff or HeckeOperator instead.
    
    The optional parameter B is a basis which can be used to increase
    precision. If B is not provided, we attempt to use a basis of the
    parent space if it's been computed.  
  }

  Mk := Parent(f);
  M := Parent(Mk);
  F := BaseField(M);
  Cl, mp := NarrowClassGroup(F);
  ZF := Integers(F);
  k := Weight(f);
  k0 := Max(k);
  chi := Character(Mk);
  K := CoefficientRing(f);

  prec := Precision(f) div Norm(mm);
  coeffs := AssociativeArray();

  for bb in NarrowClassGroupReps(M) do
    bbp := NarrowClassGroupRepsToIdealDual(M)[bb];
    bbpinv := bbp^(-1);
    coeffs[bb] := AssociativeArray();

    for nu in FunDomainRepsUpToPrec(M, bb, prec) do
      nn := nu*bbpinv;
      c := 0;

      // loop over divisors
      // Formula 2.23 in Shimura - The Special Values
      // of the zeta functions associated with Hilbert Modular Forms
      for aa in Divisors(ZF!!(nn + mm)) do
        if nn eq 0*ZF then
          //takes care if the coefficients for the zero ideal are different
          c +:= StrongMultiply([* chi(aa), Norm(aa)^(k0 - 1), Coefficients(f)[NarrowClassRepresentative(M, bb*mm/aa^2)][ZF!0] *] : K:=K);
        else
          cf := Coefficient(f, ZF!!(aa^(-2) * nn * mm));
          c +:= StrongMultiply([* chi(aa), Norm(aa)^(k0 - 1), cf *] : K:=K);
        end if;
      end for;
      a_nu := IdlCoeffToEltCoeff(c, nu, k, K);
      coeffs[bb][nu] := a_nu;
      assert a_nu in K;
    end for;
  end for;

  g := HMF(Mk, coeffs : prec:=prec, coeff_ring := K);

  // Apply basis precision increase if available
  basis := GetBasisForPrecisionIncrease(Mk, f, B);
  g := ApplyBasisPrecisionIncrease(g, basis);
  
  return g;
end intrinsic;


///////////// Eigenbasis computation ////////////////

// This code computes an eigenbasis for a Hecke-stable space 
// of meromorphic ModFrmHilDElt objects by examining the action
// on the Fourier coefficients. 
//
// For most applications, the ModFrmHil/ or Trace.m code should be used. 

intrinsic Eigenbasis(M::ModFrmHilD, basis::SeqEnum[ModFrmHilDElt] : P := 60, coprime_only:=true) -> SeqEnum[ModFrmHilDElt]
  {
    inputs:
      M: A space of forms on which the Hecke algebra acts by
           commuting self-adjoint operators.
      basis: A sequence of linearly independent ModFrmHilDElts
             whose span is preserved by all the Hecke operators.
      P: The largest norm of a prime ideal we check to establish a simultaneous eigenbasis
    returns:
      A sequence of HMFs which are an eigenbasis for the Hecke operators of primes
      up to P. The forms are normalized where possible.
  }
  MGRng := Parent(M);
  N := Level(M);
  F := BaseField(MGRng);
  ZF := Integers(F);
  hecke_matrices := [];

  primes := (coprime_only) select PrimesUpTo(P, F : coprime_to:=N) else PrimesUpTo(P, F);
  for pp in primes do
    Append(~hecke_matrices, HeckeMatrix(basis, pp));
  end for;

  // B stores a matrix such that B * M * B^-1 is
  // diagonal for every Hecke matrix M. 
  // If e_i denotes the ith standard basis vector
  // and v_i denotes the ith eigenvector in the 
  // given basis, then this means that B^-1 e_i = v_i. 
  // Therefore, the ith column of B^-1 is v_i.
  _, B := Diagonalization(hecke_matrices);
  Binv := B^-1;

  // coefficient ring of eigenforms
  L := Parent(B[1][1]);
  if F eq Rationals() then
    K := L;
  elif L eq Rationals() then
    K := F;
  elif IsSubfield(F, L) then
    K := L;
  elif IsSubfield(L, F) then
    K := F;
  else
    K := Compositum(F, L);
  end if;
   
  basis := [ChangeCoefficientRing(f, K) : f in basis];
  K := CoefficientRing(basis[1]);
  eigs := [];

  // the columns of P should be the coefficients
  // of linear combinations of basis vectors giving
  // rise to eigenvectors
  // TODO is there really no way to get the columns of an AlgMatElt? 
  for v in Rows(Transpose(Binv)) do
    eig := &+[StrongCoerce(K, v[i]) * basis[i] : i in [1 .. #basis]];
    for nn in IdealsUpTo(Norm(N), F) do
      if not IsZero(Coefficient(eig, nn)) then
        first_nonzero_a_nn := Coefficient(eig, nn);
        break;
      end if;
    end for;
    Append(~eigs, eig / first_nonzero_a_nn);
  end for;
  return eigs;
end intrinsic;

// Helper function to handle common basis logic for precision increase
function GetBasisForPrecisionIncrease(Mk, f, B)
  basis := false;
  if B cmpne false then
    // if a basis is given, we assume that it's
    // Hecke stable
    basis := B;
  elif assigned Mk`CuspFormBasis then
    // if f is a cusp form
    if #LinearDependence(Append(Mk`CuspFormBasis, f)) eq 1 then
      basis := Mk`CuspFormBasis;
    end if;
  elif assigned Mk`Basis then
    basis := Mk`Basis;
  end if;
  return basis;
end function;

// Helper function to apply basis precision increase if available
function ApplyBasisPrecisionIncrease(g, basis)
  if basis cmpne false then
    g := IncreasePrecisionWithBasis(g, basis);
  end if;
  return g;
end function;

intrinsic HeckeOperatorCoeff(f::ModFrmHilDElt, pi : B:=false) -> ModFrmHilDElt
  {
    Hecke operator for nonparitious forms using coefficient access.
    This is specialized for fields with narrow class number 1.
  }

  require Type(pi) in [FldOrdElt, FldNumElt, RngOrdElt, RngQuadElt, FldElt, FldQuadElt] : "pi must be a RngOrdElt, FldOrdElt or FldNumElt, not", Type(pi);
  Mk := Parent(f);
  M := Parent(Mk);
  F := BaseField(M);
  ZF := Integers(F);
  // nonparitious code is only implemented for fields of
  // narrow class number 1
  assert NarrowClassNumber(F) eq 1;
  bb := 1*ZF;
  k := Weight(f);
  chi := Character(Mk);
  K := CoefficientRing(f);

  // for now we assume this f is a cusp form
  assert IsZero(Coefficient(f, bb, F!0));
  // for now this operator is only defined for pi a totally positive generator of 
  // a prime ideal
  assert FieldOfFractions(Parent(pi)) eq F;
  assert IsIntegral(pi);
  pp := ideal<ZF | ZF!pi>;
  assert IsPrime(pp);
  assert IsTotallyPositive(pi);

  prec := Precision(f) div Norm(pp);
  coeffs := AssociativeArray();
  coeffs[bb] := AssociativeArray();

  for nu in FunDomainRepsUpToPrec(M, bb, prec) do
    nn := M`RepToIdeal[bb][nu];
    if IsZero(nn) then
      coeffs[bb][nu] := K!0;
    else
      auts := AutsOfKReppingEmbeddingsOfF(F, F);
      pi_to_k := &*[auts[i](pi)^(k[i] - 1) : i in [1 .. #k]];
      a_nu := Coefficient(f, bb, pi * nu);
      if nn subset pp then
        a_nu +:= StrongMultiply([* chi(pp), pi_to_k, Coefficient(f, bb, nu / pi) *] : K:=K);
      end if;
      assert a_nu in K;
      coeffs[bb][nu] := a_nu;
    end if;
  end for;

  g := HMF(Mk, coeffs : prec:=prec, coeff_ring := K);

  // Apply basis precision increase if available
  basis := GetBasisForPrecisionIncrease(Mk, f, B);
  g := ApplyBasisPrecisionIncrease(g, basis);
  
  return g;
end intrinsic;

// Hecke operator that automatically chooses between paritious and nonparitious methods
intrinsic HeckeOperator(f::ModFrmHilDElt, nn::RngOrdIdl : B:=false) -> ModFrmHilDElt, .
  {
    Hecke operator that automatically handles both paritious and nonparitious forms.
    For paritious forms, uses the standard ideal-based method and returns only the transformed form.
    For nonparitious forms, requires nn to be a prime ideal, uses Fourier coefficient method,
    and returns both the transformed form and the totally positive generator pi.
  }
  Mk := Parent(f);
  k := Weight(Mk);
  
  if IsParitious(k) then
    return HeckeOperatorIdeal(f, nn : B:=B), _;
  else
    // For nonparitious forms, we need nn to be a prime ideal
    // and we extract a totally positive generator
    require IsPrime(nn) : "For nonparitious forms, nn must be a prime ideal";
    F := BaseField(Parent(Mk));
    ZF := Integers(F);
    
    // Get a totally positive generator of the prime ideal
    // This assumes narrow class number 1
    require NarrowClassNumber(F) eq 1 : "Nonparitious forms only supported for narrow class number 1";
    
    b, pi := IsNarrowlyPrincipal(nn);
    require b : "Prime ideal should be narrowly principal when narrow class number is 1";
    require IsTotallyPositive(pi) : "Generator must be totally positive";
    
    return HeckeOperatorCoeff(f, pi : B:=B), pi;
  end if;
end intrinsic;

intrinsic HeckeMatrix(basis::SeqEnum[ModFrmHilDElt], nn::RngOrdIdl) -> Mtrx
  {
    inputs:
      basis: A sequence of linearly independent ModFrmHilDElts
             whose span is preserved by all the Hecke operators.
      nn: An integral ideal indexing the Hecke operator
    returns:
      A matrix over corresponding to the action of the Hecke operator on
      this space. 
  }

  assert #LinearDependence(basis) eq 0;
  rows := [];

  for f in basis do
    g, _ := HeckeOperator(f, nn);
    lindep := LinearDependence(basis cat [g]);
    require #lindep eq 1 : "Try increasing precision, #lindep was", #lindep;
    lindep := lindep[1];
    // We will transpose at the end. 
    // For now, each row stores the
    // coefficients of the linear combination 
    // of basis vectors which give rise to g
    Append(~rows, [-1 * lindep[i] / lindep[#basis + 1] : i in [1 .. #basis]]);
  end for;

  return Transpose(Matrix(rows));
end intrinsic;

intrinsic HeckeMatrix(Mk::ModFrmHilD, nn::RngOrdIdl) -> Mtrx
  {
    inputs:
      Mk: A space of HMFs
      nn: An integral ideal indexing the Hecke operator
    returns:
      A matrix over corresponding to the action of the Hecke operator on
      this space. 
  }
  return HeckeMatrix(Basis(Mk));
end intrinsic;
