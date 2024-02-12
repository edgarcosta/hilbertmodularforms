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
      coeffs[n] := &*[coeffs[pair[1]^pair[2]] : pair in factorization(n)];
    end if;
  end for;
end intrinsic;

intrinsic CuspFormFromEigenvalues(
    Mk::ModFrmHilD,
    coeffs_by_nn::Assoc :
    coeff_ring := DefaultCoefficientRing(Mk)
    ) -> ModFrmHilDElt
  {
    inputs:
      Mk - Space of HMFs
      coeffs_by_nn - Poorly named, but this is an associative array
        indexed by prime ideals pp up to Precision(Parent(Mk))
      coeff_ring - coefficient ring of these cusp forms
    returns:
      The cusp form with these Hecke eigenvalues
  }
  M := Parent(Mk);
  F := BaseField(Mk);
  ExtendMultiplicatively(
    ~coeffs_by_nn,
    Level(Mk),
    Weight(Mk),
    Character(Mk),
    PrimeIdeals(M),
    Ideals(M) :
    factorization:=func<n|Factorization(M, n)>
    );

  // TODO abhijitm once Jean's improvements are in, this construction
  // should be rewritten
  coeffs_by_nu := AssociativeArray();
  
  for bb in NarrowClassGroupReps(M) do
    coeffs_by_nu[bb] := AssociativeArray();
    coeffs_by_nu[bb][F!0] := coeff_ring!0;
  end for;

  ideals := Exclude(Ideals(M), ideal<Integers(F) | 0>);

  for nn in ideals do
    a_nn := coeffs_by_nn[nn];
    bb := IdealToNarrowClassRep(M, nn);
    nu := IdealToRep(M)[bb][nn];
    coeffs_by_nu[bb][nu] := IdlCoeffToEltCoeff(a_nn, nu, Weight(Mk), coeff_ring);
  end for;

  return HMF(Mk, coeffs_by_nu : coeff_ring := coeff_ring);
end intrinsic;
