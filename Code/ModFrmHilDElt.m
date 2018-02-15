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
  {check compatibility and coefficient equality up to minimum precision.}
  prec, which_one := Min([Precision(f), Precision(g)]);
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


intrinsic GetCoefficient(f::ModFrmHilDElt, I::RngOrdIdl) -> RngOrdElt
  {returns a_I}
  return Coefficients(f)[Dictionary(f)[I]];
end intrinsic;

intrinsic SetCoefficient(f::ModFrmHilDElt, I::RngOrdIdl, c::RngOrdElt)
  {sets a_I to c}
  f`Coefficients[Dictionary(f)[I]] := c;
end intrinsic;

intrinsic GetCoefficient(f::ModFrmHilDElt, nu::RngOrdElt) -> RngOrdElt
  {returns a_nu}
  if not assigned Parent(f)`Representatives then
    error "You must first equip the space with a multiplication table";
  end if;
  return Coefficients(f)[DictionaryRepresentatives(f)[nu]];
end intrinsic;

intrinsic SetCoefficient(f::ModFrmHilDElt, nu::RngOrdElt, c::RngOrdElt)
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
  F := Parent(coeff[1]);
  G, Pmap, Gmap := AutomorphismGroup(F);
  result := [];
  for g in G do
    Append(~result, HMF(M, k, [Gmap(g)(elt) : elt in coeff]) );
  end for;
  return result;
end intrinsic;





////////// ModFrmHilDElt arithmetic //////////

intrinsic '*'(c::RngIntElt, f::ModFrmHilDElt) -> ModFrmHilDElt
  {scale f by integer c.}
  coeffs := Coefficients(f);
  ZK := Parent(coeffs[1]);
  assert Parent(c) eq ZK;
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

intrinsic '*'(f::ModFrmHilD, g::ModFrmHilD) -> ModFrmHilD
  {return f*g}
  M := Parent(f);
  assert Parent(f) eq Parent(g);
  if not assigned M`MultiplicationTable then
    error "The Parent is not equipped with a Multiplication Table!";
  end if;
  prec := Precision(M);
  fcoeffs := Coefficients(f);
  gcoeffs := Coefficients(g);
  ZC := Parent(fcoeffs[0]);
  MTable := MultiplicationTable(M);
  assert ZC eq Parent(gcoeffs[0]);
  coeffs := [ZC!0 :  i in [1..#Coefficients(f)[0]]];
  for i := 1 to #Coefficients(f)[0] do
    c := ZC!0;
    for pair in MTable[i] do
      c +:= fcoeffs[ pair[1] ] * gcoeffs[ pair[2] ];
    end for;
    coeffs[i] := c;
  end for;
  kf := Weight(f);
  kg := Weight(g);
  k := [ kf[i] + kf[g] : i in [1..#kf] ];
  return HMF(M, k, coeffs);
end intrinsic;


// FIXME: this should be RngOrd
intrinsic '!'(R::Rng, f::ModFrmHilDElt) -> ModFrmHilDElt
{
  {returns f such that a_I := R!a_I}
  coeffs := [R!c : c in Coefficients(f)];
  return HMF(Parent(f), Weight(f), coeffs);
end intrinsic;
