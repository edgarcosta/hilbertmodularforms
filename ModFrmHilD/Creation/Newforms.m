import "../../ModFrmHil/diamond.m" : HeckeCharacterSubspace;

////////// Creation of CuspForms from ModFrmHilDElt //////////



intrinsic ExtendMultiplicatively(~coeffs::Assoc, N::RngOrdIdl, k::RngIntElt, prime_ideals::SeqEnum, ideals::SeqEnum[RngOrdIdl] : factorization:=false)
  { set a_nn := prod(a_p^e : (p,e) in factorization(nn) }
  // TODO: take character into acount
  if factorization cmpeq false then
    factorization := Factorization;
  end if;

  //TODO: take ideals[n] = Factorization(n), and make use of M`IdealsFactorization

  // set recursion
  // ideals must be sorted by Norm
  max_norm := Norm(ideals[#ideals]);
  prec := Floor(Log(2, max_norm)) + 1;
  Q := Rationals();
  // Power series ring for recursion
  QX<X, Y> := PolynomialRing(Q, 2);
  R<T> := PowerSeriesRing(QX : Precision := prec);
  recursion := Coefficients(1/(1 - X*T + Y*T^2));
  // If good, then 1/(1 - a_p T + Norm(p) T^2) = 1 + a_p T + a_{p^2} T^2 + ...
  // If bad, then 1/(1 - a_p T) = 1 + a_p T + a_{p^2} T^2 + ...
  for p in prime_ideals do
    Np := Norm(p);
    if N subset p then
      Npk := 0;
    else
      Npk := Np^(k - 1);
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
      coeffs[pe] := Evaluate(recursion[e+1], [coeffs[p], Npk]);
    end for;
  end for;
  // extend multiplicatively
  for n in ideals do
    if not IsDefined(coeffs, n) then
      coeffs[n] := &*[coeffs[pair[1]^pair[2]] : pair in factorization(n)];
    end if;
  end for;
end intrinsic;

intrinsic Eigenform(Mk::ModFrmHilD, EigenValues::Assoc) -> ModFrmHilDElt
  {given a_p constructs the modular form}
  require IsTrivial(DirichletRestriction(Character(Mk))) : "Only implemented for character whose Dirichlet restriction is trivial";
  k := Weight(Mk);
  require #SequenceToSet(k) eq 1 : "Only implemented for parallel weight";
  k := k[1];
  N := Level(Mk);

  ZF := Integers(Mk);
  // a_0 and a_1
  M := Parent(Mk);
  coeffs := EigenValues;
  coeffs[0*ZF] := 0;
  coeffs[1*ZF] := 1;


  function factorization(n)
    return Factorization(M, n);
  end function;
  ExtendMultiplicatively(~coeffs, N, k, PrimeIdeals(M), Ideals(M) : factorization:=factorization);

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

intrinsic Eigenform(Mk::ModFrmHilD, f::ModFrmHilElt) -> ModFrmHilDElt
  {return the inclusions of f, as ModFrmHilElt, into M}
  require IsEigenform(f): "The form must be an eigenform";
  M := Parent(Mk);
  N2 := Level(Mk);
  N1 := Level(Parent(f));
  require N2 eq N1: "The level of f must match the level of the target ambient space";

  vprintf HilbertModularForms: "Computing eigenvalues for %o...\n", f;
  ev := AssociativeArray();
  vtime HilbertModularForms:
  for pp in PrimeIdeals(M) do
   ev[pp] := HeckeEigenvalue(f, pp);
  end for;

  return Eigenform(Mk, ev);
end intrinsic;



// By doing all inclusions at once, we s that we only need to compute the
intrinsic OldEigenformInclusions(Mk::ModFrmHilD, f::ModFrmHilElt) -> ModFrmHilDElt
  {return the inclusions of f, as ModFrmHilElt, into M}
  M := Parent(Mk);
  N2 := Level(Mk);
  N1 := Level(Parent(f));
  require N2 subset N1: "The level of f must divide the level of the target ambient space";
  require IsEigenform(f): "The form must be an eigenform";
  k := Weight(Parent(f));
  require k eq Weight(Mk): "The weight of the form and space do not match";
  require #SequenceToSet(k) eq 1 : "Only implemented for parallel weight";
  k := k[1];

  coeffs := AssociativeArray();
  for pp in PrimeIdeals(M) do
   coeffs[pp] := HeckeEigenvalue(f, pp);
  end for;
  F := BaseField(M);
  ZF := Integers(F);
  coeffs[0*ZF] := 0;
  coeffs[1*ZF] := 1;
  divisors := Divisors(N2/N1);
  ideals := &cat[[ZF !! (nn*ddinv) : nn in Ideals(M) | IsIntegral(nn*ddinv)] where ddinv := dd^-1 : dd in divisors];
  // remove duplicates
  ideals := SetToSequence(SequenceToSet(ideals));
  norms := [CorrectNorm(I) : I in ideals];
  ParallelSort(~norms, ~ideals);
  primes := SetToSequence(SequenceToSet(&cat[[fac[1] : fac in Factorization(M, nn)] : nn in ideals | not IsZero(nn)]));
  function factorization(nn)
    return Factorization(M, nn);
  end function;

  ExtendMultiplicatively(~coeffs, N1, k, primes, ideals : factorization:=factorization);

  res := [];
  for dd in Divisors(N2/N1) do
    ddinv := dd^-1;
    // coefficients by bb
    CoeffsArray := AssociativeArray();
    for bb in NarrowClassGroupReps(M) do
      CoeffsArray[bb] := AssociativeArray();
      for nu->nn in ShintaniRepsIdeal(M)[bb] do
        nnddinv := nn * ddinv;
        if IsIntegral(nnddinv) then
          nnddinv := ZF !! nnddinv;
          bool, v := IsDefined(coeffs, ZF !! nn*ddinv);
        else
          v := 0;
        end if;
        CoeffsArray[bb][nu] := bool select v else 0;
      end for;
    end for;
    Append(~res, HMF(Mk, CoeffsArray));
  end for;
  return res;
end intrinsic;

intrinsic OldCuspForms(MkN1::ModFrmHilD, MkN2::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  {return the inclusion of MkN1 into MkN2}
  require Weight(MkN1) eq Weight(MkN2) : "the weights must match";
  require BaseField(MkN1) eq BaseField(MkN2) : "the base fields must match";
  M := Parent(MkN1);
  F := BaseField(M);
  ZF := Integers(F);
  N1 := Level(MkN1);
  N2 := Level(MkN2);
  require N2 subset N1: "the level of the first argument must divide the level of the second argument";
  require N2 ne N1: "the level of the first argument must differ from the level of the second argument";
  return &cat[OldEigenformInclusions(MkN2, f) : f in MagmaNewCuspForms(MkN1)];
end intrinsic;

intrinsic MagmaNewformDecomposition(Mk::ModFrmHilD) -> List
  {return the NewformDecomposition in magma type}
  require IsTrivial(DirichletRestriction(Character(Mk))): "We only support Newforms for characters with trivial Dirichlet restriction, as we rely on the magma functionality";
  if not assigned Mk`MagmaNewformDecomposition then
    N := Level(Mk);
    k := Weight(Mk);
    vprintf HilbertModularForms: "Decomposing HilbertCuspForms for N=%o and weight=%o...", IdealOneLine(N), k;
    M := Parent(Mk);
    F := BaseField(M);
    vprintf HilbertModularForms: "creating ";
    MF := HilbertCuspForms(Mk);
    vprintf HilbertModularForms: "new ";
    New := NewSubspace(MF);
    vprintf HilbertModularForms: "hecke character subspace ";
    S := HeckeCharacterSubspace(New, Character(Mk));
    vprintf HilbertModularForms: "decomposition...";
    vtime HilbertModularForms:
    Mk`MagmaNewformDecomposition := NewformDecomposition(S);
    vprintf HilbertModularForms: "Done\n";
  end if;
  return Mk`MagmaNewformDecomposition;
end intrinsic;

intrinsic MagmaNewCuspForms(Mk::ModFrmHilD) -> SeqEnum[ModFrmHilElt]
  {return the eigenforms in magma type}
  require IsTrivial(DirichletRestriction(Character(Mk))): "We only support Newforms for characters with trivial Dirichlet restriction, as we rely on the magma functionality";
  if not assigned Mk`MagmaNewCuspForms then
    N := Level(Mk);
    k := Weight(Mk);
    vprintf HilbertModularForms: "Computing eigenforms for N=%o and weight=%o...", IdealOneLine(N), k;
    vtime HilbertModularForms:
    Mk`MagmaNewCuspForms := [* Eigenform(U) :  U in MagmaNewformDecomposition(Mk) *];
  end if;
  return Mk`MagmaNewCuspForms;
end intrinsic;




intrinsic NewCuspForms(Mk::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  {returns Hilbert newforms}
  return [Eigenform(Mk, f) : f in MagmaNewCuspForms(Mk)];
end intrinsic;


intrinsic GaloisOrbitDescentNewCuspForms(Mk::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  {return Galois descent of Hilbert newforms}
  return &cat[GaloisOrbitDescentEigenForm(Mk, d) : d in MagmaNewformDecomposition(Mk)];
end intrinsic;


intrinsic GaloisOrbitDescentEigenForm(Mk::ModFrmHilD, S::ModFrmHil) -> SeqEnum[ModFrmHilDElt]
  {return Galois descent of a Hilbert newform}
  vprintf HilbertModularForms: "Computing rational basis for %o...", S;
  M := Parent(Mk);
  // find a single generator
  p := PreviousPrime(Random(B,2*B) : Proof:=false) where B is Round(2^22.5);
  vprintf HilbertModularForms: "Finding single generator for Hecke algebra  ...";
  vtime HilbertModularForms:
  for pp in PrimeIdeals(M) do
      Tpp := HeckeOperator(S, pp);
      if Degree(MinimalPolynomial(ChangeRing(Tpp, GF(p)))) eq Dimension(S) then
          zeta_p := pp;
          Tzeta := Tpp;
          break;
      end if;
  end for;
  // _, gens := Explode(hecke_algebra(S));
  // assert #gens eq 1;
  // zeta_p := gens[1];
  Tzeta := HeckeOperator(S, zeta_p);
  Tzeta_powers := [Tzeta^i : i in [0..Dimension(S) - 1]];

  M := Parent(Mk);
  N2 := Level(Mk);
  N1 := Level(S);
  require N2 eq N1: "The level of f must match the level of the target ambient space";
  k := Weight(Mk);
  require #SequenceToSet(k) eq 1 : "Only implemented for parallel weight";
  k := k[1];

  vprintf HilbertModularForms: "Computing HeckeOperators ...";
  HeckeOperators := AssociativeArray();
  vtime HilbertModularForms:
  for pp in PrimeIdeals(M) do
   HeckeOperators[pp] := Matrix(HeckeOperator(S, pp));
  end for;
  ZF := Integers(Mk);
  // a_0 and a_1
  M := Parent(Mk);
  coeffs := HeckeOperators;
  coeffs[0*ZF] := 0;
  coeffs[1*ZF] := 1;
  function factorization(n)
    return Factorization(M, n);
  end function;
  vprintf HilbertModularForms: "Extending Hecke operators multiplicatevely...";
  vtime HilbertModularForms:
  ExtendMultiplicatively(~coeffs, N1, k, PrimeIdeals(M), Ideals(M) : factorization:=factorization);


  res := [];
  for i in [1..Dimension(S)] do
    // coefficients by bb
    CoeffsArray := AssociativeArray();
    for bb in NarrowClassGroupReps(M) do
      CoeffsArray[bb] := AssociativeArray();
      for nu->nn in ShintaniRepsIdeal(M)[bb] do
        CoeffsArray[bb][nu] := Trace(Tzeta_powers[i]*coeffs[nn]);
      end for;
    end for;
    Append(~res, HMF(Mk, CoeffsArray));
  end for;
  return res;
end intrinsic;
