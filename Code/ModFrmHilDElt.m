/*****
ModFrmHilDElt
*****/

////////// ModFrmHilDElt attributes //////////

declare type ModFrmHilDElt;
declare attributes ModFrmHilDElt:
  Parent, // M
  Weight, // SeqEnum[RngIntElt] : a sequence of [ModFrmHilDBaseField : QQ] integers
  Coefficients; // SeqEnum : this also keeps track of coefficient ring

////////// ModFrmHilDElt fundamental intrinsics //////////

intrinsic Print(f::ModFrmHilDElt : num_coeffs := 10)
  {}
  M := Parent(f);
  ideals := Ideals(M);
  k := Weight(f);
  prec := Precision(f);
  coeffs := Coefficients(f);
  printf "Hilbert modular form expansion with precision %o.\n", prec;
  printf "\nWeight: \n%o", k;
  printf "\nParent: \n%o", M;
  printf "\nCoefficients:";
  printf "\n\t(Norm, nn)  |--->   a_nn";
  printf "\n\t(%o, %o)  |--->   %o", 0,  Generators(ideals[1]), coeffs[1];
  for i:= 2 to Min(num_coeffs, #coeffs) do
    printf "\n\t(%o, %o)  |--->   %o", Norm(ideals[i]),  Generators(ideals[i]), coeffs[i];
  end for;
end intrinsic;

intrinsic 'in'(x::., y::ModFrmHilDElt) -> BoolElt
  {}
  return false;
end intrinsic;

intrinsic IsCoercible(x::ModFrmHilDElt, y::.) -> BoolElt, .
  {}
  return false;
end intrinsic;

intrinsic 'eq'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> BoolElt
  {compares Parent, Weight, and Coefficients.}
  if Parent(f) ne Parent(g) then
    return false;
  end if;
  if Weight(f) ne Weight(g) then
    return false;
  end if;
  if Coefficients(f) ne Coefficients(g) then
    return false;
  end if;
  return true;
end intrinsic;

////////// ModFrmHilDElt access to attributes //////////

intrinsic Parent(f::ModFrmHilDElt) -> ModFrmHilD
  {returns ModFrmHilD space where f lives.}
  return f`Parent;
end intrinsic;

intrinsic Weight(f::ModFrmHilDElt) -> SeqEnum[RngIntElt]
  {returns weight of f.}
  return f`Weight;
end intrinsic;

intrinsic Coefficients(f::ModFrmHilDElt) -> SeqEnum
  {returns coefficients of f as SeqEnum.}
  return f`Coefficients;
end intrinsic;

intrinsic CoefficientsParent(f::ModFrmHilDElt) -> SeqEnum
  {returns coefficients of f as SeqEnum.}
  return Parent(f`Coefficients[1]);
end intrinsic;

intrinsic BaseField(f::ModFrmHilDElt) -> FldNum
  {returns base field of parent of f.}
  return BaseField(Parent(f));
end intrinsic;

intrinsic Level(f::ModFrmHilDElt) -> RngOrdIdl
  {returns level of parent of f.}
  return Level(Parent(f));
end intrinsic;

intrinsic Precision(f::ModFrmHilDElt) -> RngIntElt
  {returns precision of parent of f.}
  return Precision(Parent(f));
end intrinsic;

intrinsic Ideals(f::ModFrmHilDElt) -> SeqEnum[RngOrdIdl]
  {returns ideals indexing f up to bound on the norm.}
  return Ideals(Parent(f));
end intrinsic;

intrinsic Dictionary(f::ModFrmHilDElt) -> Assoc
  {returns dictionary of (parent of) f.}
  return Dictionary(Parent(f));
end intrinsic;



////////// ModFrmHilDElt elementary creation functions //////////

intrinsic ModFrmHilDEltInitialize() -> ModFrmHilDElt
  {Create an empty ModFrmHilDElt object.}
  M := New(ModFrmHilDElt);
  return M;
end intrinsic;

intrinsic ModFrmHilDEltCopy(f::ModFrmHilDElt) -> ModFrmHilDElt
  {new instance of ModFrmHilDElt.}
  g := ModFrmHilDEltInitialize();
  for attr in GetAttributes(Type(f)) do
    if assigned f``attr then
      g``attr := f``attr;
    end if;
  end for;
  return g;
end intrinsic;


intrinsic HMF(M::ModFrmHilD, k::SeqEnum[RngIntElt], coeffs::SeqEnum) -> ModFrmHilDElt
  {Given M and a SeqEnum of coefficients, return ModFrmHilDElt with parent M.
  WARNING: user is responsible for coefficients and order...proceed with caution.
  }
  // assertions
  ideals := Ideals(M);
  if #coeffs ne #ideals then
    error "not the right amount of coefficients to match precision of M.";
  end if;
  assert #k eq Degree(BaseField(M));
  // make form f
  f := ModFrmHilDEltInitialize();
  f`Parent := M;
  f`Weight := k;
  f`Coefficients := coeffs;
  return f;
end intrinsic;

intrinsic HMF(M::ModFrmHilD, k::SeqEnum[RngIntElt], cmap::Assoc) -> ModFrmHilDElt
  {given a ModFrmHilD, a weight k, and an associative array of coefficients on the ideals, return ModFrmHilDElt.}
  ideals := Ideals(M);
  if #Keys(cmap) ne #ideals then
    error "not the right amount of coefficients to match precision of M.";
  end if;
  dict_ideal := Dictionary(M);
  coeffs_seqenum := [ cmap[ideals[i]]  : i in [1..#Keys(cmap)] ];
  return HMF(M, k, coeffs_seqenum);
end intrinsic;

intrinsic HMFZero(M::ModFrmHilD, k::SeqEnum[RngIntElt]) -> ModFrmHilDElt
  {create zero ModHilFrmDElt of weight k.}
  coeffs := [ 0 : i in [1..#Ideals(M)]];
  return HMF(M, k, coeffs);
end intrinsic;




////////// ModFrmHilDElt user convenience functions //////////


intrinsic GetCoefficient(f::ModFrmHilDElt, I::RngOrdIdl) -> RngElt
  {returns a_I}
  return Coefficients(f)[Dictionary(f)[I]];
end intrinsic;

intrinsic SetCoefficient(f::ModFrmHilDElt, I::RngOrdIdl, c::RngElt)
  {sets a_I to c}
  f`Coefficients[Dictionary(f)[I]] := c;
end intrinsic;

intrinsic GetCoefficient(f::ModFrmHilDElt, nu::RngOrdElt) -> RngElt
  {returns a_nu}
  if not assigned Parent(f)`Representatives then
    error "You must first equip the space with a multiplication table";
  end if;
  return Coefficients(f)[DictionaryRepresentatives(f)[nu]];
end intrinsic;

intrinsic SetCoefficient(f::ModFrmHilDElt, nu::RngOrdElt, c::RngElt)
  {sets a_nu to c}
  if not assigned Parent(f)`Representatives then
    error "You must first equip the space with a multiplication table";
  end if;
  f`Coefficients[DictionaryRepresentatives(f)[nu]] := c;
end intrinsic;

intrinsic GetCoefficientsIdeal(f::ModFrmHilDElt) -> Assoc
  {given a ModFrmHilDElt, return associative array of coefficients on the ideals.}
  coeffs := Coefficients(f);
  ideals := Ideals(f);
  result := AssociativeArray();
  for i := 1 to #ideals do
    result[ideals[i]] := coeffs[i];
  end for;
  return result;
end intrinsic;

intrinsic GetCoefficientsRepresentatives(f::ModFrmHilDElt) -> Assoc
  {given a ModFrmHilDElt, return associative array of coefficients on the representatives.}
  if not assigned Parent(f)`Representatives then
    error "You must first equip the space with a multiplication table";
  end if;
  coeffs := Coefficients(f);
  reps := Representatives(f);
  result := AssociativeArray();
  for i := 1 to #reps do
    result[reps[i]] := coeffs[i];
  end for;
  return result;
end intrinsic;

////////// ModFrmHilDElt creation functions //////////


intrinsic EigenformToHMF(M::ModFrmHilD, k::SeqEnum[RngIntElt], hecke_eigenvalues::Assoc) -> ModFrmHilDElt
  {Construct the ModFrmHilDElt in M determined (on prime ideals up to norm prec) by hecke_eigenvalues.}
  // pull info from M
  F := BaseField(M);
  N := Level(M);
  prec := Precision(M);
  // a prime
  pp := Random(Keys(hecke_eigenvalues));
  // assertions
  if not Set(PrimesUpTo(prec, F)) subset Keys(hecke_eigenvalues) then
    print "Not enough primes";
    assert false;
  end if;

  k0 := Max(k);

  // power series ring
  log_prec := Floor(Log(prec)/Log(2)); // prec < 2^(log_prec+1)
  ZK := Parent(hecke_eigenvalues[pp]);
  ZKX<X, Y> := PolynomialRing(ZK, 2);
  R<T> := PowerSeriesRing(ZKX : Precision := log_prec + 1);
  // If good, then 1/(1 - a_p T + Norm(p) T^2) = 1 + a_p T + a_{p^2} T^2 + ...
  // If bad, then 1/(1 - a_p T) = 1 + a_p T + a_{p^2} T^2 + ...
  recursion := Coefficients(1/(1 - X*T + Y*T^2));
  ideals := Ideals(M);
  coeffs := [ZK!0: i in ideals];
  set := [false : c in coeffs];
  coeffs[1] := 0; //a_0
  coeffs[2] := 1; //a_1
  set[1] := true;
  set[2] := true;
  dict := Dictionary(M);
  for i := 1 to #coeffs do
    if not set[i] then
      // is[i] is a prime
      pp := ideals[i];
      assert IsPrime(pp);
      coeffs[i] := hecke_eigenvalues[pp];
      set[i] := true;
      Np := Norm(pp)^(k0-1);
      // if pp is bad
      if N subset pp then
        Np := 0;
      end if;

      r := 2;
      pp_power := pp * pp;
      //deals with powers of p
      while pp_power in Keys(dict) do
        ipower := dict[pp_power];
        coeffs[ipower] := Evaluate(recursion[r + 1], [coeffs[i], Np]);
        set[ipower] := true;
        pp_power *:= pp;
        r +:= 1;
      end while;

      //deal with multiples of its powers by smaller numbers
      for j := 3 to #coeffs do
        if set[j] and not (ideals[j] subset pp) then
          mm := ideals[j];
          pp_power := pp;
          mmpp_power := mm * pp_power;
          while mmpp_power in Keys(dict) do
            l := dict[mmpp_power];
            assert set[l] eq false;
            ipower := dict[pp_power];
            // a_{m * pp_power} := a_{m} * a_{pp_power}
            coeffs[l] := coeffs[j] * coeffs[ipower];
            set[l] := true;
            mmpp_power *:= pp;
            pp_power *:= pp;
          end while;
        end if; //check if it's set
      end for; //loop in j

    end if; // check if it's set
  end for; // loop in i
  for i := 1 to #coeffs do
    assert set[i];
  end for;
  return HMF(M, k, coeffs);
end intrinsic;

intrinsic NewformsToHMF(M::ModFrmHilD, k::SeqEnum[RngIntElt]) -> SeqEnum[ModFrmHilDElt]
  {returns Hilbert newforms}
  F := BaseField(M);
  N := Level(M);
  prec := Precision(M);
  MF := HilbertCuspForms(F, N, k);
  S := NewSubspace(MF);
  newspaces  := NewformDecomposition(S);
  newforms := [* Eigenform(U) : U in newspaces *];
  eigenvalues := AssociativeArray();
  primes := PrimesUpTo(prec, F);
  HMFnewforms := [];
  for newform in newforms do
    for pp in primes do
        eigenvalues[pp] := HeckeEigenvalue(newform, pp);
    end for;
    ef := EigenformToHMF(M, k, eigenvalues);
    Append(~HMFnewforms, ef);
  end for;
  return HMFnewforms;
end intrinsic;

intrinsic GaloisOrbit(f::ModFrmHilDElt) -> SeqEnum[ModFrmHilDElt]
  {returns the full Galois orbit of a modular form}
  M := Parent(f);
  k := Weight(f);
  coeff := Coefficients(f);
  K := NumberField(CoefficientsParent(f));
  G, Pmap, Gmap := AutomorphismGroup(K);
  result := [];
  for g in G do
    Append(~result, HMF(M, k, [Gmap(g)(elt) : elt in coeff]) );
  end for;
  return result;
end intrinsic;

intrinsic GaloisOrbitDescent(f::ModFrmHilDElt) -> SeqEnum[ModFrmHilDElt]
  {returns the full Galois orbit of a modular form over Q}
  M := Parent(f);
  k := Weight(f);
  coeff := Coefficients(f);
  K := NumberField(CoefficientsParent(f));
  result := [];
  for b in Basis(K) do
    Append(~result, HMF(M, k, [Trace(b * elt) : elt in coeff]) );
  end for;
  return result;
end intrinsic;

intrinsic CuspFormBasis(M::ModFrmHilD, k::SeqEnum[RngIntElt]) -> SeqEnum[ModFrmHilDElt], RngIntElt
  {returns a basis for M of weight k}
  prec := Precision(M);
  F := BaseField(M);
  N := Level(M);
  ideals := Ideals(M);
  dict := Dictionary(M);
  set_ideals := Keys(dict);
  zero_coeffs := [0 : i in [1..#ideals]];
  basis := [];
  //TODO we should sieve
  for dd in Divisors(N) do
    basis := [];
    Mdd := HMFSpace(F, dd, prec);
    orbit_representatives := NewformsToHMF(Mdd, k);
    orbits := [GaloisOrbitDescent(elt) : elt in orbit_representatives];
    old_space_basis := &cat orbits;
    old_space_coeffs := [Coefficients(elt) : elt in old_space_basis];
    for ee in Divisors(N/dd) do
      new_coeffs_ee := [ zero_coeffs : i in [1..#old_space_basis]];
      for i := 1 to #ideals do
        Iee := ideals[i]*ee;
        if Iee in set_ideals then
          Iee_cord := dict[Iee];
          for j := 1 to #old_space_basis do
            new_coeffs_ee[j][Iee_cord] := old_space_coeffs[j][i];
          end for;
        else
          //this assumes ideals are sorted by norm!!
          break i;
        end if;
      end for;
      basis := basis cat [HMF(M, k, elt) : elt in new_coeffs_ee];
    end for;
    if dd eq Level(M) then
      newforms_dimension := &+[ #orbit : orbit in orbits];
    end if;
  end for;
  return basis, newforms_dimension;
end intrinsic;

intrinsic HeckeOperator(f::ModFrmHilDElt, nn::RngOrdIdl) -> ModFrmHilDElt
  {returns T(n)(f) for the trivial character}
  return HeckeOperator(f, nn, HeckeCharacterGroup(Level(f))! 1);
end intrinsic;

intrinsic HeckeOperator(f::ModFrmHilDElt, nn::RngOrdIdl, chi::GrpHeckeElt) -> ModFrmHilDElt
  {returns T(n)(f)}
  M := Parent(f);
  fcoeffs := Coefficients(f);
  ideals := Ideal(f);
  dict := Dictionary(f);
  ZC := Parent(fcoeffs[1]);
  k0 := Max(Weight(f));
  coeffs := [ZC!0 : i in [1..#fcoeffs]];
  for i:=1 to #ideals do
    c := 0;
    // loop over divisors
    // Formula 2.23 in Shimura - The Special Values of the zeta functions associated with Hilbert Modular Forms
    for aa in Divisors(ideals[i] + nn) do
      c +:= chi(aa) * Norm(aa)^(k0 - 1) * fcoeffs[ dict[ aa^(-2) * (ideals[i] * nn)]];
      end for;
    coeffs[i] := c;
    end for;
  return HMF(M, Weight(f), coeffs);
end intrinsic;

// TODO save ideal class rep to space
// FIXME
intrinsic EisensteinSeries(M::ModFrmHilD, eta::GrpHeckeElt, psi::GrpHeckeElt, k::SeqEnum[RngIntElt]) -> ModFrmHilDElt
  {}
  n := Degree(BaseField(M));
  assert #SequenceToSet(k) eq 1;
  assert k[1] ge 2; // we can remove this later
  nn := Level(M);
  aa := Conductor(eta);
  bb := Conductor(psi);
  assert nn subset aa;
  assert nn subset bb;
  Haa := HeckeCharacterGroup(aa);
  Hbb := HeckeCharacterGroup(bb);
  ideals := Ideals(M);
  coeffs := [ 0 : i in [1..#ideals]];
  assert IsPrimitive(eta*psi^-1);
  // constant term
  if aa eq ideal<Order(aa)|1> then
    prim := AssociatedPrimitiveCharacter(psi*eta^(-1));
    // zCC := 2^(-n)*eta^(-1)(tt)*LSeries(prim, 1-k);
    Lf := LSeries(prim);
    zCC := 2^(-n)*Evaluate(Lf, 1-k[1]);
    precCC := Precision(zCC);
    zCC := ComplexField(precCC)!zCC;
    // zCC := 2^(-n)*Evaluate(LSeries(eta*psi^-1), 1-k);
    bl, QQ, v, conj, _ := MakeK(zCC, 1);
    coeffs[1] := RecognizeOverK(zCC, QQ, v, conj);
  else
    coeffs[1] := 0;
  end if;
  // other terms
  for i := 2 to #ideals do // 2 here assumes #Cl = 1 FIXME
    mm := ideals[i];
    sum := 0;
    for rr in Divisors(mm) do
      sum +:= eta(mm/rr)*psi(rr)*Norm(rr^(k[1]-1));
    end for;
    coeffs[i] := sum;
  end for;
  return HMF(M, k, coeffs);
end intrinsic;

////////// ModFrmHilDElt arithmetic //////////

intrinsic '*'(c::RngIntElt, f::ModFrmHilDElt) -> ModFrmHilDElt
  {scale f by integer c.}
  coeffs := Coefficients(f);
  ZK := Parent(coeffs[1]);
  assert c in ZK;
  czk := ZK ! c;
  new_coeffs := [ czk * elt : elt in coeffs];
  return HMF(Parent(f), Weight(f), new_coeffs);
end intrinsic;


intrinsic '+'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> ModFrmHilDElt
  {return f+g.}
  assert Parent(f) eq Parent(g);
  assert Weight(f) eq Weight(g);
  new_coeffs := [ Coefficients(f)[i] + Coefficients(g)[i] : i in [1..#Coefficients(f)] ];
  return HMF(Parent(f), Weight(f), new_coeffs);
end intrinsic;

intrinsic '-'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> ModFrmHilDElt
  {return f-g.}
  assert Parent(f) eq Parent(g);
  assert Weight(f) eq Weight(g);
  new_coeffs := [ Coefficients(f)[i] - Coefficients(g)[i] : i in [1..#Coefficients(f)] ];
  return HMF(Parent(f), Weight(f), new_coeffs);
end intrinsic;

intrinsic '*'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> ModFrmHilDElt
  {return f*g}
  M := Parent(f);
  assert Parent(f) eq Parent(g);
  if not assigned M`MultiplicationTable then
    HMFEquipWithMultiplication(M);
  end if;
  prec := Precision(M);
  fcoeffs := Coefficients(f);
  gcoeffs := Coefficients(g);
  ZC := Parent(fcoeffs[1]);
  MTable := MultiplicationTable(M);
  assert ZC eq Parent(gcoeffs[1]);
  coeffs := [ZC!0 :  i in [1..#fcoeffs]];
  for i := 1 to #fcoeffs do
    c := ZC!0;
    for pair in MTable[i] do
      c +:= fcoeffs[ pair[1] ] * gcoeffs[ pair[2] ];
    end for;
    coeffs[i] := c;
  end for;
  kf := Weight(f);
  kg := Weight(g);
  k := [ kf[i] + kg[i] : i in [1..#kf] ];
  return HMF(M, k, coeffs);
end intrinsic;

intrinsic '!'(R::Rng, f::ModFrmHilDElt) -> ModFrmHilDElt
  {returns f such that a_I := R!a_I}
  coeffs := [R!c : c in Coefficients(f)];
  return HMF(Parent(f), Weight(f), coeffs);
end intrinsic;

intrinsic '!'(M::ModFrmHilD, elt::FldNumElt) -> ModFrmHilDElt
{
  {returns f such that a_0 := c with weight = [0,...,0]}
  P := Parent(elt);
  coeffs := [P!0 : c in [1..Ideals(M)]];
  coeffs[1] := elt;
  k := [0 : c in [1..Degree(BaseField(M))]];
  return HMF(M, k , coeffs);
end intrinsic;


intrinsic IsCoercible(M::ModFrmHilD, f::.) -> BoolElt, .
  {}
  if Type(f) ne ModFrmHilDElt then
    return false;
  end if;

  if Parent(f) eq M then
    return true, f;
  elif (BaseField(M) eq BaseField(f)) and (Precision(M) eq Precision(f)) then
    if Level(M) subset Level(f) then
      coeffs := Coefficients(f);
      return true, HMF(M, Weight(f) , coeffs);
    else
      return false;
    end if;
  else
    return false;
  end if;
end intrinsic;

/*
intrinsic '!'(M::ModFrmHilD, f::ModFrmHilDElt) -> ModFrmHilDElt
{
  {returns f with parent M}
  nn := Level(M);
  nnf := Level(f);
  assert nn subset nnf; // nnf divides nn
  coeffs := Coefficients(f);
  return HMF(M, Weight(f) , coeffs);
end intrinsic;
*/
