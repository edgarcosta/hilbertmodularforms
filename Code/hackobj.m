/*****
ModFrmHilD
*****/

////////// ModFrmHilD attributes //////////

declare type ModFrmHilD [ModFrmHilDElt];
declare attributes ModFrmHilD:
  Field, // FldNum : totally real field
  Level, // RngOrdIdl : ideal of Integers(Field)
  MaxPrecision, // RngIntElt : precision for the expansion
  Ideals, // SeqEnum[RngOrdIdl]
  Dictionary, // Assoc maps Ideals[i] to i

////////// ModFrmHilD fundamental intrinsics //////////

intrinsic Print(M::ModFrmHilD)
  {}
  printf "Space of Hilbert modular forms over %o.\n", M`Field;
  printf "MaxPrecision: %o\n", M`MaxPrecision;
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

// TODO
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
      if M1``attr ne M2``attr then
        return false;
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

intrinsic MaxPrecision(M::ModFrmHilD) -> RngOrgIdl
  {The MaxPrecision of the space M of Hilbert modular forms.}
  return M`MaxPrecision;
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

intrinsic HMFSpace(F::FldNum, N::RngOrdIdl, max_prec::RngIntElt) -> ModFrmHilD
  {Generates the space ModFrmHilD over F with level N.}
  assert IsTotallyReal(F);
  assert NumberField(Order(N)) eq F;
  M := ModFrmHilDInitialize();
  // field
  M`Field := F;
  // level
  M`Level := N;
  // max_prec
  M`MaxPrecision := max_prec;
  // ideals
  Is := IdealsUpTo(max_prec, F);
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

////////// ModFrmHilD convenience functions //////////
// TODO

/*****
ModFrmHilDElt
*****/

////////// ModFrmHilDElt attributes //////////

declare type ModFrmHilDElt;
declare attributes ModFrmHilDElt:
  Parent, // M
  Precision, // RngIntElt
  Weight, // SeqEnum[RngIntElt] : a sequence of [ModFrmHilDBaseField : QQ] integers
  Coefficients; // SeqEnum[RngOrdElt] or SeqEnum[RngIntElt]

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
  for i:= 1 to Min(num_coeffs, #coeffs) do
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

intrinsic Precision(f::ModFrmHilDElt) -> RngIntElt
  {returns precision of expansion for f which bounds the norm of ideals in the expansion.}
  return f`Precision;
end intrinsic;

intrinsic Weight(f::ModFrmHilDElt) -> SeqEnum[RngIntElt]
  {returns weight of f.}
  return f`Weight;
end intrinsic;

intrinsic Coefficients(f::ModFrmHilDElt) -> SeqEnum
  {returns coefficients of f.}
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

intrinsic MaxPrecision(f::ModFrmHilDElt) -> RngIntElt
  {returns max_prec of parent of f.}
  return MaxPrecision(Parent(f));
end intrinsic;

intrinsic Ideals(f::ModFrmHilDElt) -> SeqEnum[RngOrdIdl]
  {returns ideals indexing f up to bound on the norm.}
  return Ideals(Parent(f));
end intrinsic;

intrinsic Dictionary(f::ModFrmHilDElt) -> Assoc
  {returns dictionary of (parent of) f.}
  return Dictionary(Parent(f));
end intrinsic;

////////// ModFrmHilDElt creation functions //////////

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

intrinsic HMFZero(F::FldNum, N::RngOrdIdl, k::SeqEnum[RngIntElt], K::FldNum, prec::RngIntElt) -> ModFrmHilDElt
  {creates the zero ModFrmHilDElt over F with level N, weights k, coefficient ring ZK, and precision prec.}
  // parent, coefficient ring, precision
  parent := HMFSpace(F, N, k, K);
  f := ModFrmHilDEltInitialize();
  f`Parent := parent;
  ZK := Integers(K);
  f`Precision := prec;
  Is := IdealsUpTo(prec, F);
  f`Ideals := Is;
  coeffs := [ZK!0 : i in [1..#Is]];
  f`Coefficients := coeffs;
  dictionary := AssociativeArray();
  for i := 1 to #Is do
    dictionary[Is[i]] := i;
  end for;
  f`Dictionary := dictionary;
  return f;
end intrinsic;

intrinsic HMFZero(F::FldNum, N::RngOrdIdl, k::SeqEnum[RngIntElt], K::FldRat, prec::RngIntElt) -> ModFrmHilDElt
  {creates the zero ModFrmHilDElt over F with level N, weights k, coefficient ring ZZ, and precision prec.}
  // parent, coefficient ring, precision
  parent := HMFSpace(F, N, k, K);
  f := ModFrmHilDEltInitialize();
  f`Parent := parent;
  ZK := Integers(K);
  f`Precision := prec;
  // coefficients
  Is := IdealsUpTo(prec, F);
  f`Ideals := Is;
  coeffs := [ZK!0 : i in [1..#Is]];
  f`Coefficients := coeffs;
  dictionary := AssociativeArray();
  for i := 1 to #Is do
    dictionary[Is[i]] := i;
  end for;
  f`Dictionary := dictionary;
  return f;
end intrinsic;

// TODO other assertions? Is all this checking efficient enough?
intrinsic HMF(F::FldNum, N::RngOrdIdl, k::SeqEnum[RngIntElt], K::FldNum, coeffs::Assoc, prec::RngIntElt) -> ModFrmHilDElt
  {creates the corresponding ModFrmHilDElt with some sanity checking.}
  // parent, coefficient ring, precision
  parent := HMFSpace(F, N, k, K);
  f := ModFrmHilDEltInitialize();
  f`Parent := parent;
  ZK := Integers(K);
  f`Precision := prec;
  // coefficients
  Is := Keys(coeffs); // pull from given coeffs
  IsUpTo := IdealsUpTo(prec, F);
  assert Is eq IsUpTo; // index set of Is should be the same as Ideals of F up to prec
  for I in Is do
    assert Order(I) eq Integers(F);
    assert NumberField(Order(I)) eq F; // Ideals indexing the associative array are ideals of ZF
    assert Order(coeffs[I]) eq ZK;
  end for;
  f`Coefficients := coeffs;
  return f;
end intrinsic;

intrinsic EigenformToHMF(M::ModFrmHilD, k::SeqEnum[RngIntElt], hecke_eigenvalues::Assoc, prec::RngIntElt) -> ModFrmHilDElt
  {Construct the ModFrmHilDElt in M determined (on prime ideals up to norm prec) by hecke_eigenvalues.}
  // pull info from M
  F := BaseField(M);
  N := Level(M);
  // a prime
  pp := Random(Keys(hecke_eigenvalues));
  ZK := Parent(hecke_eigenvalues[pp]);
  K := NumberField(ZK);
  // assertions
  assert Keys(hecke_eigenvalues) eq Set(PrimesUpTo(prec, F));
  // create the new element
  f := HMFZero(F, N, k, K, prec);
  //FIXME
  //assert Parent(f) eq M;

  //only parallel weight
  for elt in k do
    assert elt eq k[1];
  end for;

  // power series ring
  log_prec := Floor(Log(prec)/Log(2)); // prec < 2^(log_prec+1)
  ZKX<X, Y> := PolynomialRing(ZK, 2);
  R<T> := PowerSeriesRing(ZKX : Precision := log_prec + 1);
  // If good, then 1/(1 - a_p T + Norm(p) T^2) = 1 + a_p T + a_{p^2} T^2 + ...
  // If bad, then 1/(1 - a_p T) = 1 + a_p T + a_{p^2} T^2 + ...
  recursion := Coefficients(1/(1 - X*T + Y*T^2));
  ideals := Ideals(f);
  coeffs := [ZK!0: i in ideals];
  set := [false : c in coeffs];
  coeffs[1] := 1;
  set[1] := true;
  dict := Dictionary(f);
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
      for j := 2 to #coeffs do
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
  f`Coefficients := coeffs;
  return f;
end intrinsic;

intrinsic NewformsToHMF(M::ModFrmHilD, k::SeqEnum[RngIntElt], prec::RngIntElt) -> SeqEnum[ModFrmHilDElt]
  {returns Hilbert newforms}
  F := BaseField(M);
  N := Level(M);
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
    ef := EigenformToHMF(M, k, eigenvalues, prec);
    Append(~HMFnewforms, ef);
  end for;
  return HMFnewforms;
end intrinsic;

////////// ModFrmHilDElt arithmetic //////////

intrinsic '*'(c::RngIntElt, f::ModFrmHilDElt) -> ModFrmHilDElt
  {scale f by integer c.}
  g := ModFrmHilDEltCopy(f); // new instance of f
  ZK := CoefficientRing(g);
  assert Parent(c) eq ZK;
  coeffs := Coefficients(g);
  Is := Ideals(g);
  for i := 1 to #Is do
    coeffs[i] *:= ZK!(c);
  end for;
  g`Coefficients := coeffs;
  return g;
end intrinsic;

intrinsic '*'(c::RngOrdElt, f::ModFrmHilDElt) -> ModFrmHilDElt
  {scale f by integral element c.}
  g := ModFrmHilDEltCopy(f); // new instance of f
  ZK := CoefficientRing(g);
  assert Parent(c) eq ZK;
  coeffs := Coefficients(g);
  Is := Ideals(g);
  for i := 1 to #Is do
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
  k := Weight(M);
  ZK := CoefficientRing(M);
  K := NumberField(ZK);
  // precision
  prec_f := Precision(f);
  prec_g := Precision(g);
  prec := Min([prec_f, prec_g]);
  // create new expansion h with correct parent and precision
  h := HMFZero(F, N, k, K, prec);
  // overkill assertions
  assert ZK eq CoefficientRing(f);
  assert ZK eq CoefficientRing(g);
  assert ZK eq CoefficientRing(h);
  coeffs_f := Coefficients(f);
  coeffs_g := Coefficients(g);
  Is_f := Ideals(f);
  Is_g := Ideals(g);
  Is_h := Ideals(h);
  assert Is_f eq Is_g;
  assert Is_f eq Is_h;
  Is := Is_h;
  // create coefficients
  coeffs := Coefficients(h);
  for i := 1 to #Is do
    coeffs[i] := ZK!(ZK!(coeffs_f[i])+ZK!(coeffs_g[i]));
  end for;
  h`Coefficients := coeffs;
  return h;
end intrinsic;

intrinsic '*'(f::ModFrmHilD, g::ModFrmHilD) -> ModFrmHilD
  {return f*g}
  error "multiplication of HMF expansions not implemented yet!";
end intrinsic;
