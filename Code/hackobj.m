/*****
ModFrmHilD
*****/

////////// ModFrmHilD attributes //////////

declare type ModFrmHilD [ModFrmHilDElt];
declare attributes ModFrmHilD:
  Field, // FldNum : totally real field
  Level, // RngOrdIdl : ideal of Integers(Field)
  Precision, // RngIntElt : precision for all expansions with this parent
  Ideals, // SeqEnum[RngOrdIdl]
  Dictionary; // Assoc maps Ideals[i] to i

////////// ModFrmHilD fundamental intrinsics //////////

intrinsic Print(M::ModFrmHilD)
  {}
  printf "Space of Hilbert modular forms over %o.\n", M`Field;
  printf "Precision: %o\n", M`Precision;
  printf "Level: (Norm, Ideal) = (%o, %o)\n", Norm(M`Level),  Generators(M`Level);
end intrinsic;

intrinsic 'in'(f::., M::ModFrmHilD) -> BoolElt
  {}
  if Type(f) ne ModFrmHilDElt then
    return false, "The first argument should be a ModFrmHilDElt";
  else
    return Parent(f) eq M;
  end if;
end intrinsic;

// currently this checks everything is equal except dictionaries
intrinsic 'eq'(M1::ModFrmHilD, M2::ModFrmHilD) -> BoolElt
  {True iff every attribute of M1 is equal to the corresponding attribute of M2.}
  ass_attrs_M1 := [];
  ass_attrs_M2 := [];
  all_attrs := GetAttributes(Type(M1));
  for attr in all_attrs do
    if assigned M1``attr then
      Append(~ass_attrs_M1, attr);
    end if;
    if assigned M2``attr then
      Append(~ass_attrs_M2, attr);
    end if;
  end for;
  if ass_attrs_M1 ne ass_attrs_M2 then
    return false;
  else
    for attr in ass_attrs_M1 do
      if attr ne "Dictionary" then
        if M1``attr ne M2``attr then
          return false;
        end if;
      end if;
    end for;
    // if we make it through the loop return true
    return true;
  end if;
end intrinsic;

// TODO see classical case /Applications/Magma/package/Geometry/ModFrm/creation.m
intrinsic IsCoercible(M::ModFrmHilD, f::.) -> BoolElt, .
  {}
  if Type(f) eq ModFrmHilDElt and Parent(f) eq M then
    return true, f;
  end if;
  return false;
end intrinsic;

////////// ModFrmHilD access to attributes //////////

intrinsic BaseField(M::ModFrmHilD) -> FldAlg
  {The base field of the space M of Hilbert modular forms.}
  return M`Field;
end intrinsic;

intrinsic Level(M::ModFrmHilD) -> RngOrgIdl
  {The level of the space M of Hilbert modular forms.}
  return M`Level;
end intrinsic;

intrinsic Precision(M::ModFrmHilD) -> RngOrgIdl
  {The Precision of the space M of Hilbert modular forms.}
  return M`Precision;
end intrinsic;

intrinsic Ideals(M::ModFrmHilD) -> RngOrgIdl
  {The Ideals of the space M of Hilbert modular forms.}
  return M`Ideals;
end intrinsic;

intrinsic Dictionary(M::ModFrmHilD) -> RngOrgIdl
  {The dictionary for ideals of the space M of Hilbert modular forms.}
  return M`Dictionary;
end intrinsic;

////////// ModFrmHilD creation functions //////////

intrinsic ModFrmHilDInitialize() -> ModFrmHilD
  {Create an empty ModFrmHilD object.}
  M := New(ModFrmHilD);
  return M;
end intrinsic;

intrinsic HMFSpace(F::FldNum, N::RngOrdIdl, prec::RngIntElt) -> ModFrmHilD
  {Generates the space ModFrmHilD over F with level N.}
  assert IsTotallyReal(F);
  assert NumberField(Order(N)) eq F;
  M := ModFrmHilDInitialize();
  // field
  M`Field := F;
  // level
  M`Level := N;
  // prec
  M`Precision := prec;
  // ideals
  zero_ideal := ideal<Integers(F)|0>;
  Is := [zero_ideal] cat IdealsUpTo(prec, F);
  M`Ideals := Is;
  dictionary := AssociativeArray();
  for i := 1 to #Is do
    dictionary[Is[i]] := i;
  end for;
  M`Dictionary := dictionary;
  return M;
end intrinsic;

intrinsic ModFrmHilDCopy(M::ModFrmHilD) -> ModFrmHilD
  {new instance of ModFrmHilD.}
  M1 := ModFrmHilDInitialize();
  for attr in GetAttributes(Type(M)) do
    if assigned M``attr then
      M1``attr := M``attr;
    end if;
  end for;
  return M1;
end intrinsic;

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

// TODO
intrinsic 'eq'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> BoolElt
  {check compatibility and coefficient equality up to minimum precision.}
  prec, which_one := Min([Precision(f), Precision(g)]);
  if Parent(f) ne Parent(g) then
    return false;
  else
    coeffs_f := Coefficients(f);
    coeffs_g := Coefficients(g);
    if which_one eq 1 then // f has smaller precision
      Is := Keys(coeffs_f);
      prec := Precision(f);
    else // g has smaller precision
      assert which_one eq 2;
      Is := Keys(coeffs_g);
      prec := Precision(g);
    end if;
    for I in Is do
      if coeffs_f[I] ne coeffs_g[I] then
        return false;
      end if;
    end for;
    // if we make it out of the loop then return true
    return true;
  end if;
end intrinsic;

// TODO
intrinsic Preceq(f::ModFrmHilDElt, g::ModFrmHilDElt) -> BoolElt
  {check compatibility and coefficient equality and see if both have the same precision.}
  if Precision(f) ne Precision(g) then
    return false;
  else
    if Parent(f) ne Parent(g) then
      return false;
    else
      return f eq g; // "normal equal"
    end if;
  end if;
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
    error "not enough coefficients to match precision of M.";
  end if;
  assert #k eq Degree(BaseField(M));
  // make form f
  f := ModFrmHilDEltInitialize();
  f`Parent := M;
  f`Weight := k;
  f`Coefficients := coeffs;
  return f;
end intrinsic;

intrinsic HMFZero(F::FldNum, N::RngOrdIdl, prec::RngIntElt, k::SeqEnum[RngIntElt]) -> ModFrmHilDElt
  {create zero ModHilFrmDElt of weight k.}
  M := HMFSpace(F, N, prec);
  coeffs := [];
  for i := 1 to #Ideals(M) do
    Append(~coeffs, 0);
  end for;
  return HMF(M, k, coeffs);
end intrinsic;

intrinsic HMFZero(M::ModFrmHilD, k::SeqEnum[RngIntElt]) -> ModFrmHilDElt
  {create zero ModHilFrmDElt of weight k.}
  coeffs := [];
  for i := 1 to #Ideals(M) do
    Append(~coeffs, 0);
  end for;
  return HMF(M, k, coeffs);
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

  //only parallel weight
  for elt in k do
    assert elt eq k[1];
  end for;

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
      //FIXME, only parallel weight at the moment
      Np := Norm(pp)^(k[1]-1);
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

////////// ModFrmHilDElt user convenience functions //////////

// TODO
intrinsic SetCoefficients(M::ModFrmHilD, coeffs::Assoc) -> ModFrmHilDElt
  {given a ModFrmHilD and an associative array of coefficients, return ModFrmHilDElt.}
  error "not implemented yet!";
end intrinsic;


// TODO
intrinsic GetCoefficients(f::ModFrmHilDElt) -> Assoc
  {given a ModFrmHilDElt, return associative array of coefficients.}
  error "not implemented yet!";
end intrinsic;

////////// ModFrmHilDElt arithmetic //////////

intrinsic '*'(c::RngIntElt, f::ModFrmHilDElt) -> ModFrmHilDElt
  {scale f by integer c.}
  g := ModFrmHilDEltCopy(f); // new instance of f
  coeffs := Coefficients(g);
  ZK := Parent(coeffs[1]);
  assert Parent(c) eq ZK;
  num_ideals := #Ideals(g);
  for i := 1 to num_ideals do
    coeffs[i] *:= ZK!(c);
  end for;
  g`Coefficients := coeffs;
  return g;
end intrinsic;

intrinsic '*'(c::RngIntElt, f::ModFrmHilDElt) -> ModFrmHilDElt
  {scale f by integer c.}
  g := ModFrmHilDEltCopy(f); // new instance of f
  coeffs := Coefficients(g);
  ZK := Parent(coeffs[1]);
  assert Parent(c) eq ZK;
  num_ideals := #Ideals(g);
  for i := 1 to num_ideals do
    coeffs[i] *:= ZK!(c);
  end for;
  g`Coefficients := coeffs;
  return g;
end intrinsic;

intrinsic '+'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> ModFrmHilDElt
  {return f+g.}
  assert Parent(f) eq Parent(g);
  // pull information about the ambient space
  M := Parent(f);
  F := BaseField(M);
  N := Level(M);
  // pull weight
  k_f := Weight(f);
  k_g := Weight(g);
  assert k_f eq k_g;
  k := k_f;
  // pull coefficient information
  coeffs_f := Coefficients(f);
  coeffs_g := Coefficients(g);
  ZKf := Parent(coeffs_f[1]);
  ZKg := Parent(coeffs_g[1]);
  assert ZKf eq ZKg;
  ZK := ZKf;
  // precision
  prec_f := Precision(f);
  prec_g := Precision(g);
  prec := Min([prec_f, prec_g]);
  // create new expansion h with correct parent and precision
  h := HMFZero(M, k);
  // pull ideals
  ideals_f := Ideals(f);
  ideals_g := Ideals(g);
  ideals_h := Ideals(h);
  assert #ideals_h le #ideals_f;
  assert #ideals_h le #ideals_g;
  // create coefficients
  coeffs := Coefficients(h);
  for i := 1 to #ideals_h do
    coeffs[i] := ZK!(ZK!(coeffs_f[i])+ZK!(coeffs_g[i]));
  end for;
  h`Coefficients := coeffs;
  return h;
end intrinsic;

intrinsic '*'(f::ModFrmHilD, g::ModFrmHilD) -> ModFrmHilD
  {return f*g}
  error "multiplication of HMF expansions not implemented yet!";
end intrinsic;
