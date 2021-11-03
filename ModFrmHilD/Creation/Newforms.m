

////////// Creation of CuspForms from ModFrmHilDElt //////////

intrinsic EigenformFromEigenValues(Mk::ModFrmHilD, EigenValues::Assoc) -> ModFrmHilDElt
  {given a_p constructs the modular form}
  require IsTrivial(Character(Mk)) : "Only implemented for trivial character";
  k := Weight(Mk);
  require #SequenceToSet(k) eq 1 : "Only implemented for parallel weight";
  k := k[1];
  N := Level(Mk);

  ZF := Integers(Mk);
  coeffs := AssociativeArray();
  // a_0 and a_1
  M := Parent(Mk);
  all_ideals := AllIdeals(M); // sorted by norm
  coeffs[0*ZF] := 0;
  coeffs[1*ZF] := 1;


  // set recursion
  max_norm := Norm(all_ideals[#all_ideals]);
  prec := Floor(Log(2, max_norm)) + 1;
  Q := Rationals();
  // Power series ring for recursion
  QX<X, Y> := PolynomialRing(Q, 2);
  R<T> := PowerSeriesRing(QX : Precision := prec);
  recursion := Coefficients(1/(1 - X*T + Y*T^2));
  // If good, then 1/(1 - a_p T + Norm(p) T^2) = 1 + a_p T + a_{p^2} T^2 + ...
  // If bad, then 1/(1 - a_p T) = 1 + a_p T + a_{p^2} T^2 + ...
  prime_powers := [];
  for p in AllPrimes(M) do
    Np := Norm(p);
    if N subset p then
      Npk := 0;
    else
      Npk := Np^(k - 1);
    end if;
    pe := 1;
    Npe := 1;
    for e in [1..Floor(Log(Norm(p), max_norm))] do
      pe *:= p; // p**e
      Npe *:= Np;
      // pe might not be in all_ideals, but still might show up as a factor
      if Npe gt max_norm then
        break;
      end if;
      Append(~prime_powers, <Npe, pe>);
      coeffs[pe] := Evaluate(recursion[e+1], [EigenValues[p], Npk]);
    end for;
  end for;
  // extend multiplicatively
  for n in all_ideals do
    if not IsDefined(coeffs, n) then
      coeffs[n] := &*[coeffs[pair[1]^pair[2]] : pair in Factorization(n)];
    end if;
  end for;

  // coefficients by bb
  CoeffsArray := AssociativeArray();
  for bb in NarrowClassGroupReps(M) do
    CoeffsArray[bb] := AssociativeArray();
    for nu->nn in ShintaniRepsIdeal(M)[bb] do
      CoeffsArray[bb][nu] := coeffs[nn];
    end for;
  end for;
  return HMF(Mk, CoeffsArray);
end intrinsic;


intrinsic NewformToHMF(Mk::ModFrmHilD, newform::ModFrmHilElt) -> ModFrmHilDElt
  {Construct the ModFrmHilDElt in M determined (on prime ideals up to norm prec) by hecke_eigenvalues.}
  M := Parent(Mk);
  N := Level(Mk);
  k := Weight(Mk);
  ZF := Integers(Mk);
  ev := AssociativeArray(); // eigenvalues array indexed by ideals


  // a_p for primes

  for pp in AllPrimes(M) do
    ev[pp] := HeckeEigenvalue(newform, pp);
  end for;

  return EigenformFromEigenValues(Mk, ev);
end intrinsic;


intrinsic NewformsToHMF(Mk::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  {returns Hilbert newforms}
  N := Level(Mk);
  k := Weight(Mk);
  M := Parent(Mk);
  F := BaseField(M);
  MF := HilbertCuspForms(F, N, k);
  S := NewSubspace(MF);
  newspaces  := NewformDecomposition(S);
  newforms := [* Eigenform(U) : U in newspaces *];
  HMFnewforms := [* *];
  for newform in newforms do
    NewHMF := NewformToHMF(Mk, newform);
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
