/******************************************************************************
* An HMFSerPuis is essentially a multivariate Puisex series ring over a
* coefficient ring K.  
*
* Each HMFSerPuis is attached to a GradedRingOfHMFs. In practice, forms in a given
* HMFSpace will have elements whose components lie in the HMFSerPuis with coefficient
* ring equal to the DefaultCoefficientRing of the HMFSpace.
*
* Multivariate Puiseux series are implemented as towers of Puiseux series rings, 
* and arithmetic operations within a ring work just as usual. 
*
* An HMFSerPuisElt f is mainly a wrapper around two (multivariate) Puiseux series.
* - Series(f) is a Puiseux series with monomials indexed by FunDomainReps(M), 
*   where M is the graded ring attached to the parent of f
* - ShadowSeries(f) is a Puiseux series with monomials indexed by the 
*   union of Shadows(M) and FunDomainReps(M), where M is as before.
* ShadowSeries(f) is used exclusively in multiplication and division, and 
* at all other points Series(f) is used. 
*
* The HMFSerPuisElt class essentially replaces the ModFrmHilDEltComp class which 
* used to exist. 
******************************************************************************/

declare type HMFSerPuis [HMFSerPuisElt];
declare attributes HMFSerPuis:
  CoefficientRing, // FldAlg - field K of degree n := Degree(K) in which the coefficients live
  GRng, // ModFrmHilDGradedRing - graded ring of HMFs
  RngSerPuiss; // Assoc: RngIntElt -> RngSerPuis
               
declare attributes HMFSerPuisElt:
  Parent, // HMFSerPuis
  Series, // RngSerPuisElt[RngSerPuis[...[RngSerPuis]]...]
  ShadowSeries, // RngSerPuis[RngSerPuis[...[RngSerPuis]]...]
  Precision, // RngIntElt - the maximum norm of nn for which coefficients are stored
  Space, // ModFrmHilD - the HMF space that this HMFSerPuisElt is a component in
  ComponentIdeal; // RngOrdIdl

/////////////////// HMFSerPuis constructor /////////////////// 

intrinsic cHMFSerPuis(GRng::ModFrmHilDGRng, K::Fld) -> HMFSerPuis
  {constructor}
  R := New(HMFSerPuis);
  R`GRng := GRng;
  R`CoefficientRing := K;

  // An associative array with keys [0 .. n]
  // whose value at i is a Puiseux series ring over K of "depth" i,
  // where we think of a depth 0 Puiseux series as K itself
  // and a depth k Puiseux series as a Puiseux series in k variables.
  R`RngSerPuiss := AssociativeArray();
  R`RngSerPuiss[0] := K;
  for k in [1 .. Depth(R)] do
    R`RngSerPuiss[k] := PuiseuxSeriesRing(R`RngSerPuiss[k - 1]);
    // The outermost variable is x_1 and the innermost is x_n.
    name := "x_" cat IntegerToString(Depth(R) + 1 - k);
    AssignNames(~R`RngSerPuiss[k], [name]);
  end for;
  return R;
end intrinsic;

intrinsic GetHMFSerPuis(M::ModFrmHilDGRng, coeff_ring::Fld) -> HMFSerPuis
  {}

  b, R := IsDefined(M`PuiseuxSeriesRings, DefiningPolyCoeffs(coeff_ring));
  if not b then
    R := cHMFSerPuis(M, coeff_ring);
    M`PuiseuxSeriesRings[DefiningPolyCoeffs(coeff_ring)] := R;
  end if;
  return R;
end intrinsic;

/////////////////// HMFSerPuisElt constructors /////////////////// 
 
intrinsic cHMFSerPuisElt(
    Mk::ModFrmHilD,
    bb::RngOrdIdl,
    f_ser::RngSerPuisElt :
    coeff_ring := DefaultCoefficientRing(Mk),
    prec := Parent(Mk)`Precision,
    prune := false
  ) -> HMFSerPuisElt
  { 
    Constructs an HMFSerPuisElt in R whose associated series is f. 
    This requires that f is in the multivariate Puiseux series ring
    attached to R -- coercion is handled separately.

    We can construct an HMFSerPuis from a RngSerPuisElt indexed by FunDomainReps(R`GRng)
    or from the union of Shadows(R`Grng) and FunDomainReps(R`GRng)
  }

  M := Parent(Mk);
  R := GetHMFSerPuis(M, coeff_ring);
 
  if not Parent(f_ser) eq PuiseuxRing(R) then
    // We allow the fields to be inequal as long as they
    // have the same defining polynomial, and in this case
    // we trust that Magma's automatic coercion does the right thing.
    require DefiningPolyCoeffs(CoefficientRing(f_ser)) eq DefiningPolyCoeffs(CoefficientRing(R)) :
      "The parent of f needs to be the multivariate Puiseux series ring, associated to R";

    // Since the fields have the same defining polynomial, 
    // we trust that Magma's automatic coercion does the 
    // right thing when it works.
    b, g_ser := IsCoercible(PuiseuxRing(R), f_ser);
    
    // We strong coerce if the automatic coercion fails
    if not b then
      b_2, g_ser := IsStrongCoercible(R, f_ser, prec, bb);
      require b_2 : "Something has gone wrong, this shouldn't happen!";
    end if;
    f_ser := g_ser;
  end if;

  f_HMF := New(HMFSerPuisElt);
  f_HMF`Space := Mk;
  f_HMF`Parent := R;
  f_HMF`ComponentIdeal := bb;
  f_HMF`Precision := prec;
  // TODO abhijitm optimize 
  //
  // If prune is true then f_ser has monomials corresponding to
  // extraneous terms, which we remove
  f_HMF`Series := (prune) select Series(f_ser, R, bb, prec) else f_ser;
  return f_HMF;
end intrinsic;

intrinsic cHMFSerPuisElt(
    Mk::ModFrmHilD,
    bb::RngOrdIdl,
    coeffs_by_nu::Assoc :
    coeff_ring := DefaultCoefficientRing(Mk),
    prec := Parent(Mk)`Precision
  ) -> HMFSerPuisElt
  {
    Given a parent an n-variate HMF Puiseux series ring and an associative 
    array of coefficients keyed by n-tuples of integers, creates a multivariate
    Puiseux series whose coefficient at the monomial prod_i x_i^a_i is 
    coeffs_by_nu[a_1*e_1 + ... + a_n*e_n] where e_i is a Q-basis for F.
  }
  M := Parent(Mk);
  R := GetHMFSerPuis(M, coeff_ring);

  f_ser := PuiseuxRing(R)!0;
  for nu in FunDomainRepsUpToNorm(M, bb, prec) do
    f_ser +:= RngSerPuisMonomial(R, nu, coeffs_by_nu[nu]);
  end for;

  return cHMFSerPuisElt(Mk, bb, f_ser : coeff_ring := coeff_ring, prec := prec);
end intrinsic;

intrinsic RngSerPuisMonomial(R::HMFSerPuis, nu::FldElt, a_nu::FldElt) -> RngSerPuisElt
  {
    Constructs the monomial in puis_ring representing c*q^nu. Formally, we represent
    write nu = b_1*e_1 + ... + b_n*e_n, where the e_i are a Q-basis for the
    coefficient field K associated to R and the b_i are rational numbers.
    What we actually construct is the monomial a_nu * \prod_i x_i^a_i.
  }
  b, a_nu := IsStrongCoercible(CoefficientRing(R), a_nu);
  require b : "a_nu is not strong coercible into the coefficient field of R";
  F := IndexField(R);
  tb_nu := InTraceBasis(F!nu);
  f_ser := a_nu;
  for i in [1 .. Depth(R)] do
    f_ser := elt<R`RngSerPuiss[i] | tb_nu[Depth(R) - i + 1], [f_ser], -1>;
  end for;
  return f_ser;
end intrinsic;

intrinsic RngSerPuisMonomial(Mk::ModFrmHilD, nu::FldElt, a_nu::FldElt) -> RngSerPuisElt
  {}
  M := Parent(Mk);
  R := GetHMFSerPuis(M, Parent(a_nu));
  return RngSerPuisMonomial(R, nu, a_nu);
end intrinsic;

intrinsic RngSerPuisMonomial(R::HMFSerPuis, nu::FldElt, a_nu::RngElt) -> RngSerPuisElt
  {}
  a_nu := FieldOfFractions(Parent(a_nu))!(a_nu);
  return RngSerPuisMonomial(R, nu, a_nu);
end intrinsic;

intrinsic RngSerPuisMonomial(Mk::ModFrmHilD, nu::FldElt, a_nu::RngElt) -> RngSerPuisElt
  {}
  a_nu := FieldOfFractions(Parent(a_nu))!(a_nu);
  return RngSerPuisMonomial(Mk, nu, a_nu);
end intrinsic;

intrinsic HMFSerPuisZero(Mk::ModFrmHilD, bb::RngOrdIdl) -> HMFSerPuisElt
  {
    Returns the zero element in R at the bb component.
  }
  R := GetHMFSerPuis(Parent(Mk), Rationals());
  return cHMFSerPuisElt(Mk, bb, RngSerPuisZero(R));
end intrinsic;

intrinsic RngSerPuisZero(R::HMFSerPuis) -> RngSerPuisElt
  {}
  assert elt<PuiseuxRing(R) | 0, [0], -1> eq PuiseuxRing(R)!0;
  return PuiseuxRing(R)!0;
end intrinsic;

intrinsic HMFSerPuisIdentity(Mk::ModFrmHilD, bb::RngOrdIdl) -> HMFSerPuisElt
  {
    Returns the identity element in R.
  }
  R := GetHMFSerPuis(Parent(Mk), Rationals());
  return cHMFSerPuisElt(Mk, bb, PuiseuxRing(R)!1);
end intrinsic;

intrinsic HMFIdentity(Mk::ModFrmHilD, bb::RngOrdIdl) -> HMFSerPuisElt
  {}
  M := Parent(Mk);
  R := GetHMFSerPuis(M, Rationals());
  return HMFSerPuisIdentity(R, bb);
end intrinsic;

/////////////////// HMFSerPuis and HMFSerPuisElt Access /////////////////// 

intrinsic PuiseuxRing(R::HMFSerPuis) -> RngSerPuis
  {
    Returns the depth Depth(R) multivariate Puiseux series ring 
    attached to R.
  }
  return R`RngSerPuiss[Depth(R)];
end intrinsic;

intrinsic IndexField(R::HMFSerPuis) -> Fld
  {
    Returns the field which indexes the coefficients of 
    Hilbert Fourier series in this space.
  }
  return BaseField(R`GRng);
end intrinsic;

intrinsic IndexField(f::HMFSerPuisElt) -> Fld
  {
    Returns the field which indexes the coefficients of 
    Hilbert Fourier series in this space.
  }
  return BaseField(Parent(f)`GRng);
end intrinsic;

intrinsic Depth(R::HMFSerPuis) -> RngIntElt
  {
    Returns the number of variables in the multivariate
    Puiseux series ring attached to R. This will be the
    degree of its index field.
  }
  return Degree(BaseField(R`GRng));
end intrinsic;

intrinsic CoefficientRing(f::HMFSerPuisElt) -> Fld
  {
    Returns the field in which the coefficients of f live.
  }
  return Parent(f)`CoefficientRing;
end intrinsic;

intrinsic CoefficientRing(R::HMFSerPuis) -> Fld
  {
    Returns the field in which the coefficients of f live.
  }
  return R`CoefficientRing;
end intrinsic;

intrinsic CoefficientRing(f_ser::RngSerPuisElt) -> Fld
  {
    Returns the field in which the coefficients of f live.
  }
  coeff_ring := Parent(f_ser);
  // TODO abhijitm probably a cleaner way to say "not a power series ring"
  while not (IsNumberField(coeff_ring) or coeff_ring cmpeq Rationals()) do
    coeff_ring := CoefficientRing(coeff_ring);
  end while;
  return coeff_ring;
end intrinsic;

intrinsic ComponentIdeal(f::HMFSerPuisElt) -> RngOrdIdl
  {}
  return f`ComponentIdeal;
end intrinsic;

intrinsic UnitCharacter(f::HMFSerPuisElt) -> GrpCharUnitTotElt
  {}
  return UnitCharacter(Space(f));
end intrinsic;

intrinsic Weight(f::HMFSerPuisElt) -> SeqEnum[RngIntElt]
  {}
  return Weight(Space(f));
end intrinsic;

intrinsic Level(f::HMFSerPuisElt) -> RngOrdIdl
  {}
  return Level(Space(f));
end intrinsic;

intrinsic Precision(f::HMFSerPuisElt) -> RngIntElt
  {}
  return f`Precision;
end intrinsic;

intrinsic Space(f::HMFSerPuisElt) -> ModFrmHilDElt
  {}
  if not assigned f`Space then
    return false;
  else
    return f`Space;
  end if;
end intrinsic;

intrinsic GradedRing(f::HMFSerPuisElt) -> ModFrmHilDGRng
  {}
  return Parent(f)`GRng;
end intrinsic;

/////////////////// HMFSerPuisElt - Coefficient Access /////////////////// 

intrinsic Coefficient(f::HMFSerPuisElt, nu::FldElt) -> FldElt
  {
    Returns the coefficient a_nu of q^nu in the Fourier series. 
  }
  R := Parent(f);
  F := IndexField(R);

  require Parent(nu) eq F : "The coefficient does not lie in the index field";

  return Coefficient(Series(f), Depth(R), nu);
end intrinsic;

intrinsic Coefficient(f_ser::RngSerPuisElt, depth::RngIntElt, nu::FldElt) -> FldElt
  {
    Returns the coefficient a_nu of q^nu in the Fourier series. 
  }
  // TODO abhijitm this function probably doesn't need
  // to take depth as an argument, and should have some
  // error handling.
  for i in [1 .. depth] do
    f_ser := Coefficient(f_ser, InTraceBasis(nu)[i]);
  end for;
  return f_ser;
end intrinsic;

intrinsic Coefficients(f::HMFSerPuisElt) -> Assoc
  {Temporary function to transition out of ModFrmHilDEltComp}
  M := Parent(f)`GRng;
  bb := ComponentIdeal(f);
  coeffs := AssociativeArray();
  for nu in FunDomainRepsUpToNorm(M, bb, f`Precision) do
    coeffs[nu] := Coefficient(f, nu);
  end for;
  return coeffs;
end intrinsic;

intrinsic NumberOfCoefficients(f::HMFSerPuisElt) -> RngIntElt
  {}
  M := Parent(f)`GRng;
  bb := ComponentIdeal(f);
  return #FunDomainRepsUpToNorm(M)[bb][f`Precision];
end intrinsic;

intrinsic IsZero(f::HMFSerPuisElt) -> BoolElt
  {}
  return IsZero(Series(f));
end intrinsic;

/////////////////// HMFSerPuisElt Setters /////////////////// 

intrinsic SetSpace(f::HMFSerPuisElt, space::ModFrmHilD)
  {}
  f`Space := space;
end intrinsic;

/////////////////// HMFSerPuis fundamental intrinsics /////////////////// 

intrinsic Print(R::HMFSerPuis)
  {}
  K := R`CoefficientRing;
  print "Coefficient field:", R`CoefficientRing;
  print "Depth:", Depth(R);
  print "Index field:", IndexField(R);
end intrinsic;

intrinsic 'eq'(R::HMFSerPuis, S::HMFSerPuis) -> BoolElt
  {}
  return R`CoefficientRing eq S`CoefficientRing and
    Depth(R) eq Depth(S) and
    IndexField(R) eq IndexField(S);
end intrinsic;

intrinsic IsCoercible(S::HMFSerPuis, f::.) -> BoolElt, HMFSerPuisElt
  {
    If f is an HMFSerPuisElt whose parent is an HMFSerPuis R with coefficient field
    and place (K, v) and S is an HMFSerPuis (L, w), then attempts to return
    f as an element of S.
  }
  require Type(f) eq HMFSerPuisElt : "Cannot coerce an object of type %o into an HMFSerPuis space", Type(f);

  R := Parent(f);

  // noop if f is already in S
  if R eq S then
    return true, f;
  end if;

  require R`GRng eq S`GRng : "Cannot coerce between power series rings from different\
    graded rings of HMFs.";

  K := R`CoefficientRing;
  L := S`CoefficientRing;

  bb := f`ComponentIdeal;

  f_ser := Series(f);
  b, g_ser := IsStrongCoercible(S, f_ser, Precision(f), bb);
  if not b then
    return false, _;
  end if;
  
  return true, cHMFSerPuisElt(Space(f), bb, g_ser : coeff_ring := L, prec := Precision(f));
end intrinsic;

// TODO abhijitm this function should really not need to take prec and bb 
// at all, since it's just a matter of going through monomials one by one,
// but it's annoying to implement this so for now we're doing it this way
intrinsic IsStrongCoercible(S::HMFSerPuis, f_ser::RngSerPuisElt, prec::RngIntElt, bb::RngOrdIdl) -> BoolElt, RngSerPuisElt
  {}
  g_ser := RngSerPuisZero(S);
  L := S`CoefficientRing;
  for nu in FunDomainRepsUpToNorm(S`GRng, bb, prec) do
    a_nu := Coefficient(f_ser, Depth(S), nu);
    b_nu := StrongCoerce(L, a_nu);
    // b, b_nu := IsStrongCoercible(L, a_nu);
    b := true;
    if not b then
      return false, _;
    else
      g_ser +:= RngSerPuisMonomial(S, nu, b_nu);
    end if;
  end for;
  return true, g_ser;
end intrinsic;

intrinsic 'in'(f::., R::HMFSerPuis) -> BoolElt
  {}
  if Type(f) ne HMFSerPuisElt then
    return false, "The first argument should be a HMFSerPuisElt";
  else
    return Parent(f) eq R;
  end if;
end intrinsic;

/////////////////// HMFSerPuisElt fundamental intrinsics /////////////////// 

intrinsic Print(f::HMFSerPuisElt, level::MonStgElt : num_coeffs := 10)
  {}
  if level in ["Default", "Minimal", "Maximal"] then
    prec := Precision(f);
    bb := ComponentIdeal(f);
    M := Parent(f)`GRng;
    printf "Coefficients for component ideal class bb = %o\n", bb;
    printf "\n\t(Norm, nu)  |--->   a_nu";
    count := 0;
    for nu in FunDomainRepsUpToNorm(M, bb, prec) do
      t := CorrectNorm(RepToIdeal(M)[bb][nu]);
      printf "\n\t(%o, %o)  |--->   %o", t,  nu, Coefficient(f, nu);
      count +:= 1;

      if t ge prec then
        printf "\n \t Cannot print more coefficients; precision is too small", num_coeffs;
        break;
      end if;

      if count ge num_coeffs then
        printf "\n...";
        break;
      end if;
    end for;
    printf "\n\n";
  elif level eq "Magma" then
    error "not implemented yet!";
  else
    error "not a valid printing level.";
  end if;
end intrinsic;


intrinsic Parent(f::HMFSerPuisElt) -> HMFSerPuis
  {}
  return f`Parent;
end intrinsic;

intrinsic 'eq'(f::HMFSerPuisElt, g::HMFSerPuisElt) -> BoolElt
  {}
  return (Parent(f) eq Parent(g) and Series(f) eq Series(g));
end intrinsic;

/////////////////// HMFSerPuis operations /////////////////// 

intrinsic Compositum(R::HMFSerPuis, S::HMFSerPuis) -> HMFSerPuis
  {
    Given HMFSerPuis rings R and S with coefficient fields 
    K and L, returns an HMFSerPuis ring whose coefficient
    field is the compositum KL. 
  }
  
  // if R and S are the same we do nothing
  if R eq S then
    return R;
  end if;
  K := R`CoefficientRing;
  L := S`CoefficientRing;

  M := Compositum(K, L);

  GRng := R`GRng;
  require GRng eq S`GRng : "Cannot take compositum of spaces of HMF\
    Fourier series in different graded rings.";
  return GetHMFSerPuis(GRng, M);
end intrinsic;

/////////////////// HMFSerPuisElt arithmetic /////////////////// 

intrinsic '+'(f::HMFSerPuisElt, g::HMFSerPuisElt) -> HMFSerPuisElt
  {}
  R := f`Parent;
  space := Space(f);

  // if the precisions are the same then we do not
  // have any extra monomials after adding the series
  // together, meaning that we don't need to prune
  if Precision(f) ne Precision(g) then
    prec := Min(Precision(f), Precision(g));
    prune := true;
  else
    prec := Precision(f);
    prune := false;
  end if;
  bb := f`ComponentIdeal;

  require R eq g`Parent : "We cannot add HMF series with different \
    coefficient rings";
  require space eq Space(g) : "We cannot add HMF series with different \
    coefficient rings";
  require bb eq g`ComponentIdeal : "We cannot add\
    HMF series associated to different components";

  return cHMFSerPuisElt(space, bb, Series(f) + Series(g) : 
    coeff_ring := R`CoefficientRing, prec := prec, prune := prune);
end intrinsic;

intrinsic '*'(c::FldElt, f::HMFSerPuisElt) -> HMFSerPuisElt
  {}
  R := f`Parent;
  K := R`CoefficientRing;
  b, c_K := IsStrongCoercible(K, c);

  require b : "We cannot scale an HMF by a scalar not coercible into\
    its coefficient field";

  return cHMFSerPuisElt(Space(f), f`ComponentIdeal, c_K * Series(f) : 
    coeff_ring := K, prec := Precision(f));
end intrinsic;

intrinsic '*'(c::RngElt, f::HMFSerPuisElt) -> HMFSerPuisElt
  {}
  R := f`Parent;
  K := R`CoefficientRing;
  b, c_K := IsStrongCoercible(K, c);
  require b : "We cannot scale an HMF by a scalar not coercible into\
    its coefficient field";
  return c_K * f;
end intrinsic;

intrinsic '-'(f::HMFSerPuisElt, g::HMFSerPuisElt) -> HMFSerPuisElt
  {}
  K := f`Parent`CoefficientRing;
  return f + K!(-1) * g;
end intrinsic;

intrinsic '*'(f::HMFSerPuisElt, g::HMFSerPuisElt) -> HMFSerPuisElt
  {}
  R := f`Parent;
  S := g`Parent;
  T := Compositum(R, S);
  f := T!f;
  g := T!g;
  prec := Min(Precision(f), Precision(g));
  bb := f`ComponentIdeal;

  require bb eq g`ComponentIdeal : "We cannot multiply\
    HMF series associated to different components";

  return cHMFSerPuisElt(Space(f) * Space(g), bb, ShadowSeries(f) * ShadowSeries(g) : 
    coeff_ring := T`CoefficientRing, prec := prec, prune := true);
end intrinsic;

intrinsic '^'(f::HMFSerPuisElt, n::RngIntElt) -> HMFSerPuisElt
  {}
  return cHMFSerPuisElt(Space(f)^n, f`ComponentIdeal, ShadowSeries(f)^n : 
    coeff_ring := CoefficientRing(f), prec := Precision(f), prune := true);
end intrinsic;

intrinsic '/'(f::HMFSerPuisElt, g::HMFSerPuisElt) -> HMFSerPuisElt
  {}

  require Coefficient(g, IndexField(g)!0) ne 0 : "Cannot divide by a form which is\
  zero at infinity on any component.";
  R := f`Parent;
  S := g`Parent;
  T := Compositum(R, S);
  f := T!f;
  g := T!g;
  bb := f`ComponentIdeal;
  prec := Min(Precision(f), Precision(g));

  require bb eq g`ComponentIdeal : "We cannot divide\
  HMF series associated to different components";

  return cHMFSerPuisElt(Space(f) / Space(g), bb, ShadowSeries(f) / ShadowSeries(g) : 
    coeff_ring := T`CoefficientRing, prec := prec, prune := true);
end intrinsic;

/////////////////// HMFSerPuisElt arithmetic helpers /////////////////// 

intrinsic ShadowSeries(f::HMFSerPuisElt) -> RngSerPuisElt
  {TODO}
  if not assigned f`ShadowSeries then
    f`ShadowSeries := f`Series; 
    K := CoefficientRing(f);
    R := Parent(f);
    bb := f`ComponentIdeal;
    space := Space(f);
    uc := UnitCharacters(space)[bb];
    for shadow in Shadows(Parent(f)`GRng)[bb][Precision(f)] do
      nu, eps := Explode(shadow);
      a_shadow := StrongMultiply(K, [* Coefficient(f, nu), Evaluate(uc, eps) *]);
      f`ShadowSeries +:= RngSerPuisMonomial(R, nu * eps, a_shadow);
    end for;
  end if;
  return f`ShadowSeries;
end intrinsic;

intrinsic Series(f::HMFSerPuisElt) -> RngSerPuisElt
  {TODO}
  return f`Series;
end intrinsic;

intrinsic Series(f_ser::RngSerPuisElt, R::HMFSerPuis, bb::RngOrdIdl, prec::RngIntElt) -> RngSerPuisElt
  {TODO}
  g_ser := RngSerPuisZero(R);
  for nu in FunDomainRepsUpToNorm(R`GRng, bb, prec) do
    a_nu := Coefficient(f_ser, Depth(R), nu); // this will be assigned if f`Series isn't
    g_ser +:= RngSerPuisMonomial(R, nu, a_nu);
  end for;
  return g_ser;
end intrinsic;

/////////////////// HMFSerPuisElt helpers /////////////////// 

intrinsic Trace(f::HMFSerPuisElt) -> HMFSerPuisElt 
  {return Trace(f)}
  K := DefaultCoefficientRing(Space(f));
  M := Parent(f)`GRng;
  R := GetHMFSerPuis(M, K);
  bb := ComponentIdeal(f);

  g_ser := RngSerPuisZero(R);
  for nu in FunDomainRepsUpToNorm(M, bb, f`Precision) do
    a_nu := Coefficient(f, nu);
    b_nu := (K eq Rationals()) select Trace(a_nu) else Trace(a_nu, K);
    g_ser +:= RngSerPuisMonomial(R, nu, b_nu);
  end for;
  return cHMFSerPuisElt(Space(f), ComponentIdeal(f), g_ser : coeff_ring := K, prec:=Precision(f));
end intrinsic;

intrinsic MapCoefficients(m::Map, f::HMFSerPuisElt) -> HMFSerPuisElt
  {return the ModFrmHilDEltComp where the map acts on the coefficients}
  R := Parent(f);
  M := Parent(f)`GRng;
  g_ser := RngSerPuisZero(R);
  for nu in FunDomainRepsUpToNorm(M, ComponentIdeal(f), Precision(f)) do
    a_nu := Coefficient(f, nu);
    g_ser +:= RngSerPuisMonomial(R, nu, m(a_nu));
  end for;
  return cHMFSerPuisElt(Space(f), ComponentIdeal(f), g_ser : coeff_ring := CoefficientRing(f), prec:=Precision(f));
end intrinsic;

intrinsic Inclusion(f::HMFSerPuisElt, Mk::ModFrmHilD, mm::RngOrdIdl) -> HMFSerPuisElt
  {Takes a form f(z) and produces f(mm*z) in Mk (of level NN) with component ideal class [mm*bb]}

  coeff_f := Coefficients(f);
  Mk_f := Space(f);
  M_f := Parent(Mk_f);
  M := Parent(Mk);
  N1 := Level(Mk_f);
  N2 := Level(Mk);
  chi := Character(Mk);
  chif := Character(Mk_f);
  mf, pf := Modulus(chif);
  ZF := Integers(M);
  coeff_ring := CoefficientRing(f);

  require Weight(Mk_f) eq Weight(Mk): "Weight(f) is not equal to Weight(Mk)";
  require chif eq Restrict(chi, mf, pf): "Character(f) is not equal to Character(Mk)";
  require UnitCharacters(Mk_f) eq UnitCharacters(Mk): "UnitCharacters(f) is not equal to UnitCharacters(Mk)";
  require N2 subset N1: "Level of f does not divide level of Mk";
  require N2 subset mm: "Ideal mm does not divide level of Mk";

  coeff := AssociativeArray();
  bb := ComponentIdeal(f);
  mmbb := NarrowClassRepresentative(M, mm*bb);

  mminv := mm^-1;
  for nn -> nu in IdealToRep(M)[mmbb] do
    if IsIntegral(nn*mminv) then
      // set b_nn = a_{nn/mm}
      // in terms of shintani reps
      coeff[nu] := coeff_f[IdealToRep(M)[bb][ZF!!(nn*mminv)]];
    else
      coeff[nu] := 0;
    end if;
  end for;

  return cHMFSerPuisElt(Mk, mmbb, coeff : coeff_ring := coeff_ring, prec:=Precision(f));
end intrinsic;
