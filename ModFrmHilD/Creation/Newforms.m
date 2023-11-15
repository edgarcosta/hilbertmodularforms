import "../../ModFrmHil/diamond.m" : HeckeCharacterSubspace;
import "../../ModFrmHil/copypaste/hecke.m" : hecke_algebra;

// Caching magma computations
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
    Mk`MagmaNewformDecomposition := [<elt, Character(Mk)> : elt in NewformDecomposition(S)];
    vprintf HilbertModularForms: "Done\n";
  end if;
  return Mk`MagmaNewformDecomposition;
end intrinsic;

intrinsic MagmaNewCuspForms(Mk::ModFrmHilD) -> SeqEnum[ModFrmHilElt]
  {return the eigenforms in magma type}
  if not assigned Mk`MagmaNewCuspForms then
    N := Level(Mk);
    k := Weight(Mk);
    vprintf HilbertModularForms: "Computing eigenforms for N=%o and weight=%o...", IdealOneLine(N), k;
    vtime HilbertModularForms:
    Mk`MagmaNewCuspForms := [* <Eigenform(elt[1]), elt[2]> :  elt in MagmaNewformDecomposition(Mk) *];
  end if;
  return Mk`MagmaNewCuspForms;
end intrinsic;


// Generic extending multiplicatevely
intrinsic ExtendMultiplicatively(~coeffs::Assoc, N::RngOrdIdl, k::RngIntElt, chi::., prime_ideals::SeqEnum, ideals::SeqEnum[RngOrdIdl] : factorization:=false)
  { set a_nn := prod(a_p^e : (p,e) in factorization(nn) }
  // TODO: take character into acount
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
  // If good, then 1/(1 - a_p T + Chi(p)*Norm(p) T^2) = 1 + a_p T + a_{p^2} T^2 + ...
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


// Eigenforms new/old in Mk
intrinsic Eigenforms(Mk::ModFrmHilD, f::Any, chi::GrpHeckeElt : GaloisDescent:=true) -> SeqEnum[ModFrmHilDElt]
  {
    return the inclusions of f, as ModFrmHil(Elt), into M

    Given an eigenform of type ModFrmHil (Magma's internal HMF type) 
    with coefficients in a field L/F, where F is the base field for the 
    space of HMFs, let V be the dimension [L:F] vector space of HMFs spanned 
    by f and its conjugates.

    This function returns a list of [L:F] forms of type ModFrmHilD 
    -- defined over a subfield of the splitting field of F --
    which span V. 


    In general, the field of definition will be the smallest field over which
    the Hecke operators are defined. See 
    https://magma.maths.usyd.edu.au/magma/handbook/text/1735
    for some more about this. 
  }

  if Type(f) eq ModFrmHil then
    S := f;
    if not GaloisDescent then
      f := Eigenforms(S);
    end if;
  else
    require Type(f) eq ModFrmHilElt : "f must be ModFrmHil or ModFrmHilElt";
    require IsEigenform(f): "The form must be an eigenform";
    S := Parent(f);
  end if;

  M := Parent(Mk);
  N := Level(Mk);
  NS := Level(S);
  require N subset NS :"The level must divide the level of the target ambient space";
  require AssociatedPrimitiveCharacter(chi) eq AssociatedPrimitiveCharacter(Character(Mk)): "The character of f must match the level of the target ambient space";
  require Weight(S) eq Weight(Mk): "The weight of the form and space do not match";
  require #SequenceToSet(Weight(S)) eq 1 : "Only implemented for parallel weight";
  k := Weight(S)[1];

  divisors := Divisors(N/NS);
  if N eq NS then
    primes := PrimeIdeals(M);
    ideals := Ideals(M);
  else
    ZF := Integers(Mk);
    ideals := &cat[[ZF !! (nn*ddinv) : nn in Ideals(M) | IsIntegral(nn*ddinv)] where ddinv := dd^-1 : dd in divisors];
    // remove duplicates
    ideals := SetToSequence(SequenceToSet(ideals));
    norms := [CorrectNorm(I) : I in ideals];
    ParallelSort(~norms, ~ideals);
    primes := SetToSequence(SequenceToSet(&cat[[fac[1] : fac in Factorization(M, nn)] : nn in ideals | not IsZero(nn)]));
  end if;

  if GaloisDescent then
    fn := func<pp|Matrix(HeckeOperator(S, pp))>;
    // Tzeta is the matrix of a generator for the Hecke algebra
    // (it has a generator because the Hecke algebra is isomorphic
    // to a number field). 
    T , _, _, _, _, Tzeta, _ := Explode(hecke_algebra(S : generator:=true));
    if Order(chi) in [1,2] then
      chiH := chi;
    else
      chi_copy := chi;
      Z<z> := CyclotomicField(Order(chi));
      SetTargetRing(~chi_copy, z);
      K := NumberField(MinimalPolynomial(Tzeta));
      r, m := Explode(Explode(Roots(DefiningPolynomial(Z), K)));
      assert m eq 1;
      ZtoH := hom<Z->T |  [Evaluate(Polynomial(Eltseq(r)), Tzeta)]>;
      chiH := map<Domain(chi_copy) -> Parent(Tzeta) | x :-> ZtoH(chi_copy(x))>;
    end if;
  else
    fn := func<pp|HeckeEigenvalue(f, pp)>;
    Tzeta := Matrix(HeckeEigenvalueField(S), Matrix(1,1, [1]));
    chiH := chi;
  end if;

  vprintf HilbertModularForms: "Computing eigenvalues for %o...\n", S;
  coeffs := AssociativeArray();
  vtime HilbertModularForms:
  for pp in primes do
    coeffs[pp] :=  fn(pp);
  end for;
  ZF := Integers(Mk);
  coeffs[0*ZF] := 0;
  coeffs[1*ZF] := 1;

  ExtendMultiplicatively(~coeffs, N, k, chiH, primes, ideals : factorization:=func<n|Factorization(M, n)>);

  Tzeta_powers := [Tzeta^i : i in [0..Nrows(Tzeta) - 1]];

  // the coefficient ring of the coefficients
  //
  // if we are performing GaloisDescent, 
  // the best we can do is the field over 
  // which the Hecke operators are defined
  //
  // if not, then nothing changes and we use the
  // field over which the eigenforms themselves
  // are defined
  R := GaloisDescent select Rationals() else HeckeEigenvalueField(S);

  res := [];
  for dd in divisors do
    ddinv := dd^-1;
    // coefficients by bb
    CoeffsArray := [AssociativeArray() : _ in [1..Nrows(Tzeta)]];
    for bb in NarrowClassGroupReps(M) do
      for i in [1..Nrows(Tzeta)] do
        CoeffsArray[i][bb] := AssociativeArray();
      end for;
      for nu->nn in ShintaniRepsIdeal(M)[bb] do
        nnddinv := nn * ddinv;
        if IsIntegral(nnddinv) then
          nnddinv := ZF !! nnddinv;
          bool, v := IsDefined(coeffs, ZF !! nn*ddinv);
        else
          v := 0;
        end if;
        for i in [1..Nrows(Tzeta)] do
          // Let f_j be the jth Galois conjugate of f and T a generator
          // for the Hecke algebra. Then, the ith basis vector that we output is
          // T^i * (f_1 + ... + f_n). 
          //
          // To see why this is what the code is doing, think in the eigenbasis.
          // Then, Tzeta_powers[i] = T^i is a diagonal matrix.
          // The element v is the nnth Hecke operator, or equivalently, a diagonal matrix
          // whose entries are the nnth Fourier coefficient of f_1, ..., f_n. 
          // By linearity, the trace of this product is the nnth Fourier coefficient
          // of T^i(f_1 + ... + f_n) as desired. 
          CoeffsArray[i][bb][nu] := R!(bool select Trace(Tzeta_powers[i]*v) else 0);
        end for;
      end for;
    end for;
    for i in [1..Nrows(Tzeta)] do
      Append(~res, HMF(Mk, CoeffsArray[i]));
    end for;
  end for;
  return res;
end intrinsic;



intrinsic OldCuspForms(MkN1::ModFrmHilD, MkN2::ModFrmHilD : GaloisDescent:=true) -> SeqEnum[ModFrmHilDElt]
  {return the inclusion of MkN1 into MkN2}
  require Weight(MkN1) eq Weight(MkN2) : "the weights must match";
  require BaseField(MkN1) eq BaseField(MkN2) : "the base fields must match";
  M := Parent(MkN1);
  F := BaseField(M);
  ZF := Integers(F);
  N1 := Level(MkN1);
  N2 := Level(MkN2);
  require N2 subset N1: "the level of the first argument must divide the level of the second argument";
  //require N2 ne N1: "the level of the first argument must differ from the level of the second argument";
  return &cat[Eigenforms(MkN2, elt[1], elt[2] : GaloisDescent:=GaloisDescent) : elt in MagmaNewCuspForms(MkN1)];
end intrinsic;


intrinsic NewCuspForms(Mk::ModFrmHilD : GaloisDescent:=true) -> SeqEnum[ModFrmHilDElt]
  {returns Hilbert newforms}
  return &cat[Eigenforms(Mk, elt[1], elt[2] : GaloisDescent:=GaloisDescent) : elt in MagmaNewCuspForms(Mk)];
end intrinsic;

