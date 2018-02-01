/*****
ModFrmHilD
*****/

////////// ModFrmHilD attributes //////////

declare type ModFrmHilD [ModFrmHilDElt];
declare attributes ModFrmHilD:
  Field, // FldNum : totally real field
  Level, // RngOrdIdl : ideal of Integers(Field)
  Weight, // SeqEnum[RngIntElt] : a sequence of [ModFrmHilDBaseField : QQ] integers
  CoefficientRing; // Integers() or RngOrd : Integers of a number field
  // DirichletCharacter // always assigned: either the integer 1, or a GrpDrchNFElt with modulus Level(M)
  // CentralCharachter
  // NewLevel
  // Dimension
  // QuaternionOrder
  // Ambient

////////// ModFrmHilD special intrinsics //////////

intrinsic Print(M::ModFrmHilD)
  {}
  printf "Space of Hilbert modular forms over %o.\n", M`Field;
  printf "Weight: %o\n", M`Weight;
  printf "Level: %o\n", M`Level;
  printf "CoefficientRing: %o\n", M`CoefficientRing;
end intrinsic;

intrinsic 'in'(f::., M::ModFrmHilD) -> BoolElt
  {}
  if Type(f) ne ModFrmHilDElt then
    return false, "The first argument should be a ModFrmHilDElt";
  else
    return Parent(f) eq M;
  end if;
end intrinsic;

// TODO hack for now
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

// TODO currently it is illegal to coerce expansions into spaces without matching coefficient rings.
// TODO should be coercible if coefficient rings are coercible
intrinsic IsCoercible(M::ModFrmHilD, f::.) -> BoolElt, .
  {}
  if Type(f) eq ModFrmHilDElt and Parent(f) eq M then
    return true, f;
  end if;
  return false;
end intrinsic;

////////// ModFrmHilD creation functions //////////

intrinsic ModFrmHilDInitialize() -> ModFrmHilD
  {Create an empty ModFrmHilD object.}
  M := New(ModFrmHilD);
  return M;
end intrinsic;

intrinsic HMFSpace(F::FldNum, N::RngOrdIdl, k::SeqEnum[RngIntElt], K::FldNum) -> ModFrmHilD
  {Generates the space ModFrmHilD over F with level N, weights k, and coefficient ring ZK.}
  assert IsTotallyReal(F);
  assert NumberField(Order(N)) eq F;
  assert IsAdmissibleWeight(F, k);
  M := ModFrmHilDInitialize();
  M`Field := F;
  M`Level := N;
  M`Weight := k;
  ZK := Integers(K);
  M`CoefficientRing := ZK;
  return M;
end intrinsic;

intrinsic HMFSpace(F::FldNum, N::RngOrdIdl, k::SeqEnum[RngIntElt], K::FldRat) -> ModFrmHilD
  {Generates the space ModFrmHilD over F with level N, weights k, and coefficient ring ZZ.}
  assert IsTotallyReal(F);
  assert NumberField(Order(N)) eq F;
  assert IsAdmissibleWeight(F, k);
  M := ModFrmHilDInitialize();
  M`Field := F;
  M`Level := N;
  M`Weight := k;
  ZK := Integers(K);
  M`CoefficientRing := ZK;
  return M;
end intrinsic;

intrinsic HMFSpace(F::FldNum, N::RngOrdIdl, k::SeqEnum[RngIntElt]) -> ModFrmHilD
  {Generates the space ModFrmHilD over F with level N, weights k, and coefficient ring ZZ.}
  return HMFSpace(F, N, k, Rationals());
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

////////// ModFrmHilD access to basic attributes //////////

intrinsic BaseField(M::ModFrmHilD) -> FldAlg
  {The base field of the space M of Hilbert modular forms.}
  return M`Field;
end intrinsic;

intrinsic Level(M::ModFrmHilD) -> RngOrgIdl
  {The level of the space M of Hilbert modular forms.}
  return M`Level;
end intrinsic;

intrinsic Weight(M::ModFrmHilD) -> SeqEnum[RngIntElt]
  {The weight of the space M of Hilbert modular forms.}
  return M`Weight;
end intrinsic;

intrinsic CoefficientRing(M::ModFrmHilD) -> FldAlg
  {The coefficient ring of the space M of Hilbert modular forms.}
  return M`CoefficientRing;
end intrinsic;

/*****
ModFrmHilDElt
*****/

////////// ModFrmHilDElt attributes //////////

declare type ModFrmHilDElt;
declare attributes ModFrmHilDElt:
  Parent, // M
  Precision, // RngIntElt : precision for the expansion
  Ideals, // SeqEnum[RngOrdIdl]
  Dict, // Assoc maps Ideals[i] to i
  Coefficients; // SeqEnum[RngOrdElt]

////////// ModFrmHilDElt special intrinsics //////////

// TODO print expansion more cleanly, currently just for debugging
intrinsic Print(f::ModFrmHilDElt)
  {}
  printf "Hilbert modular form expansion with precision %o.\n", f`Precision;
  printf "\nParent: \n%o", f`Parent;
  printf "\nCoefficients: \n%o\n", f`Coefficients;
end intrinsic;

intrinsic 'in'(x::., y::ModFrmHilDElt) -> BoolElt
  {}
  return false;
end intrinsic;

intrinsic IsCoercible(x::ModFrmHilDElt, y::.) -> BoolElt, .
  {}
  return false;
end intrinsic;

// TODO default way to deal with precision?
// FIXME
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

// FIXME
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

////////// ModFrmHilDElt access to basic attributes //////////

intrinsic Parent(f::ModFrmHilDElt) -> ModFrmHilD
  {returns ModFrmHilD space where f lives.}
  return f`Parent;
end intrinsic;

intrinsic Precision(f::ModFrmHilDElt) -> RngIntElt
  {returns precision of expansion for f which bounds the norm of ideals in the expansion.}
  return f`Precision;
end intrinsic;

intrinsic Coefficients(f::ModFrmHilDElt) -> SeqEnum
  {returns coefficients of f.}
  return f`Coefficients;
end intrinsic;

intrinsic BaseField(f::ModFrmHilDElt) -> FldNum
  {returns base field of parent of f.}
  return BaseField(f`Parent);
end intrinsic;

intrinsic Level(f::ModFrmHilDElt) -> RngOrdIdl
  {returns level of parent of f.}
  return Level(f`Parent);
end intrinsic;

intrinsic Weight(f::ModFrmHilDElt) -> SeqEnum[RngIntElt]
  {returns weight of parent of f.}
  return Weight(f`Parent);
end intrinsic;

intrinsic CoefficientRing(f::ModFrmHilDElt) -> Rng
  {returns coefficient ring of expansion f which is ZK or ZZ}
  return CoefficientRing(f`Parent);
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
  // coefficients
  Is := IdealsUpTo(prec, F);
  coeffs := AssociativeArray(); // empty
  for I in Is do
    coeffs[I] := ZK!0;
  end for;
  f`Coefficients := coeffs;
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
  coeffs := AssociativeArray(); // empty
  for I in Is do
    coeffs[I] := ZK!0;
  end for;
  f`Coefficients := coeffs;
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

intrinsic EigenformToHMF(M::ModFrmHilD, hecke_eigenvalues::Assoc, prec::RngIntElt) -> ModFrmHilDElt
  {Construct the ModFrmHilDElt in M determined (on prime ideals up to norm prec) by hecke_eigenvalues.}
  // pull info from M
  F := BaseField(M);
  k := Weight(M);
  N := Level(M);
  ZK := CoefficientRing(M);
  K := NumberField(ZK);
  // assertions
  primes := Keys(hecke_eigenvalues);
  primes_check := PrimesUpTo(prec, F);
  assert primes eq primes_check;
  // power series ring
  R<T> := PowerSeriesRing(ZK);
  for pp in primes do
    q := Norm(pp);
    log_prec := Floor(Log(prec)/Log(q)); // q^log_prec < prec < q^(log_prec+1)
    // TODO edgar
  end for;
  // create the new element
  f := HMFZero(F, N, k, K, prec);
  assert Parent(f) eq M;
  Is := IdealsUpTo(prec, F);
  coeffs := AssociativeArray(Is);
end intrinsic;

////////// ModFrmHilDElt arithmetic //////////

intrinsic '*'(c::RngIntElt, f::ModFrmHilDElt) -> ModFrmHilDElt
  {scale f by integer c.}
  g := ModFrmHilDEltCopy(f); // new instance of f
  ZK := CoefficientRing(g);
  assert Parent(c) eq ZK;
  coeffs := g`Coefficients;
  for I in Keys(coeffs) do // loop over ideal of F up to precision
    coeffs[I] *:= ZK!(c); // coercion here is overkill
  end for;
  g`Coefficients := coeffs; // do we need to reassign?
  return g;
end intrinsic;

intrinsic '*'(c::RngOrdElt, f::ModFrmHilDElt) -> ModFrmHilDElt
  {scale f by integral element c.}
  g := ModFrmHilDEltCopy(f); // new instance of f
  ZK := CoefficientRing(g);
  assert Parent(c) eq ZK;
  coeffs := g`Coefficients;
  for I in Keys(coeffs) do // loop over ideals of F up to precision
    coeffs[I] *:= ZK!(c); // multiplication in ZK, coercion just to be safe
  end for;
  g`Coefficients := coeffs; // do we need to reassign?
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
  ZK := M`CoefficientRing;
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
  coeffs_f := f`Coefficients;
  coeffs_g := g`Coefficients;
  // create coefficients
  coeffs := h`Coefficients;
  for I in Keys(coeffs) do
    coeffs[I] := ZK!(ZK!(coeffs_f[I])+ZK!(coeffs_g[I]));
  end for;
  h`Coefficients := coeffs;
  return h;
end intrinsic;

intrinsic '*'(f::ModFrmHilD, g::ModFrmHilD) -> ModFrmHilD
  {return f*g}
  error "multiplication of HMF expansions not implemented yet!";
end intrinsic;

////////// ModFrmHilDElt misc functions //////////

// TODO currently only allows even nonnegative...
intrinsic IsAdmissibleWeight(F::FldNum, k::SeqEnum[RngIntElt]) -> BoolElt
  {Decide if the sequence of weights k can be used for the weight of a ModFrmHilD.}
  n := Degree(F);
  if #k ne n then
    return false;
  end if;
  if Min(k) lt 0 then
    return false;
  end if;
  for wt in k do
    if IsOdd(wt) then
      return false;
    end if;
  end for;
  return true;
end intrinsic;
