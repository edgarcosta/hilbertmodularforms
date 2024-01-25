
////////// ModFrmHilDElt attributes //////////

declare attributes ModFrmHilDElt:
  Parent, // ModFrmHilD
  Components, // Assoc: bb --> f_bb, each f_bb of type ModFrmHilDEltComp
  CoefficientRing, // Rng: equal for all components
  Precision; // RngIntElt: equal for all components

////////// ModFrmHilDElt fundamental intrinsics //////////

intrinsic Print(f::ModFrmHilDElt, level::MonStgElt : num_coeffs := 10)
  {}
  if level in ["Default", "Minimal", "Maximal"] then
    Mk := Parent(f);
    M := Parent(Mk);
    bbs := NarrowClassGroupReps(M);
    k := Weight(Mk);
    N := Level(Mk);
    if level ne "Minimal" then
        printf "Hilbert modular form in %o\n", Mk;
        printf "with components:\n";
    end if;
    for bb in bbs do
        printf "\n";
      Print(Components(f)[bb], level : num_coeffs := num_coeffs);
    end for;
  elif level eq "Magma" then
    error "not implemented yet!";
  else
    error "not a valid printing level.";
  end if;
end intrinsic;


////////// ModFrmHilDElt access to attributes //////////

intrinsic Parent(f::ModFrmHilDElt) -> ModFrmHilD
  {returns ModFrmHilD space where f lives.}
  return f`Parent;
end intrinsic;

intrinsic Weight(f::ModFrmHilDElt) -> SeqEnum[RngIntElt]
  {returns weight of f.}
  return Weight(Parent(f));
end intrinsic;

intrinsic GradedRing(f::ModFrmHilDElt) -> ModFrmHilDGRng
  {return parent of parent of f}
  Mk := Parent(f);
  return Parent(Mk);
end intrinsic;

intrinsic BaseField(f::ModFrmHilDElt) -> FldNum
  {return base field of parent of f.}
  return BaseField(GradedRing(f));
end intrinsic;

intrinsic Level(f::ModFrmHilDElt) -> RngOrdIdl
  {return level of parent of f.}
  return Level(Parent(f));
end intrinsic;

intrinsic Components(f::ModFrmHilDElt) -> Assoc
  {return the components of f}
  return f`Components;
end intrinsic;

intrinsic Coefficient(f::ModFrmHilDElt, bb::RngOrdIdl, nu::RngElt) -> Any
  {}
  return Coefficient(Components(f)[bb], nu);
end intrinsic;

intrinsic Coefficient(f::ModFrmHilDElt, nn::RngOrdIdl) -> RngElt
  {}
  require not IsZero(nn) : "The zero coefficient exists on each component";
  M := Parent(Parent(f));
  nu := IdealToRep(M, nn);
  bb := IdealToNarrowClassRep(M, nn);
  return EltCoeffToIdlCoeff(Coefficient(f, bb, nu), nu, f);
end intrinsic;

intrinsic Coefficients(f::ModFrmHilDElt) -> Any
  {}
  coeffs := AssociativeArray();
  for bb in Keys(Components(f)) do
    coeffs[bb] := Coefficients(Components(f)[bb]);
  end for;
  return coeffs;
end intrinsic;

intrinsic CoefficientRing(f::ModFrmHilDElt) -> Any
  {}
  return f`CoefficientRing;
end intrinsic;

intrinsic NumberOfCoefficients(f::ModFrmHilDElt) -> Any
{}
  return &+[NumberOfCoefficients(fcomp): fcomp in Components(f)];
end intrinsic;

intrinsic Precision(f::ModFrmHilDElt) -> RngIntElt
  {}
  return f`Precision;
end intrinsic;

////////// ModFrmHilDElt creation functions //////////

// This is called by all HMF creation methods.
intrinsic HMFSumComponents(Mk::ModFrmHilD, components::Assoc) -> ModFrmHilDElt
  {
    Return the ModFrmHilDElt with parent Mk and Components components.
  }
  M := Parent(Mk);
  bbs := NarrowClassGroupReps(M);
  require Keys(components) eq SequenceToSet(bbs): "Coefficient array should be indexed by representatives of Narrow class group";

  f := New(ModFrmHilDElt);
  f`Parent := Mk;
  f`Components := AssociativeArray();
  f`CoefficientRing := CoefficientRing(components[bbs[1]]);
  f`Precision := Precision(components[bbs[1]]);

  for bb in bbs do
    f_bb := components[bb];
    require ComponentIdeal(f_bb) eq bb: "Components mismatch ideal representatives";
    require Type(f_bb) eq ModFrmHilDEltComp: "The components need to be ModFrmHilDEltComps";
    require Mk eq Space(f_bb): "The parents of the components must be all the same";
    require Precision(f_bb) eq f`Precision: "Components must have the same precision";
    require CoefficientRing(f_bb) eq f`CoefficientRing: "Components must have the same coefficient ring";
    f`Components[bb] := Copy(f_bb);
  end for;
  return f;
end intrinsic;

intrinsic HMF(Mk::ModFrmHilD,
              coeffs::Assoc
              :
              coeff_ring := DefaultCoefficientRing(Mk),
              prec := Precision(Parent(Mk))) -> ModFrmHilDElt
  {
    Return the ModFrmHilDElt with parent Mk, with the fourier coefficients given via a
    a double associative array coeffs
    and the unit characters are also given via an associative array indexed on the
    narrow class group representatives.
    Explicitly, coeffs is an double associative array
    coeffs[bb][nu] = a_(bb, nu) = a_(nu)*(bb')^-1
    for all nu in the Shintani cone.
  }

  M := Parent(Mk);
  bbs := NarrowClassGroupReps(M);
  require Keys(coeffs) eq SequenceToSet(bbs): "Coefficient array should be indexed by representatives of Narrow class group";

  components := AssociativeArray();
  for bb in bbs do
    components[bb] := HMFComponent(Mk, bb, coeffs[bb] :
                                   CoefficientRing := coeff_ring, prec := prec);
  end for;
  return HMFSumComponents(Mk, components);
end intrinsic;

//This is used in the linear algebra code
intrinsic HMF(Mk::ModFrmHilD,
              seqcoeffs::SeqEnum,
              nus::SeqEnum,
              bbs::SeqEnum
              :
              prec := Precision(Parent(Mk))
              ) -> ModFrmHilDElt
  { Return the ModFrmHilDElt with parent Mk, with the fourier coefficients given via a
    a sequence of coeff, mathching the sequence of nus and bbs }
  coeffs := AssociativeArray();
  for i->bb in bbs do
    cbb := AssociativeArray();
    k := &+[Integers() | #elt : elt in nus[1..i-1]];
    for j->nu in nus[i] do
      cbb[nu] := seqcoeffs[j + k];
    end for;
    coeffs[bb] := cbb;
  end for;
  return HMF(Mk, coeffs : prec:=prec);
end intrinsic;

intrinsic HMF(fbb::ModFrmHilDEltComp) -> ModFrmHilDElt
  {Returns the HMF equal to fbb and zero on other components}
  f := HMFZero(Space(fbb) : coeff_ring := CoefficientRing(fbb), prec := Precision(fbb));
  f`Components[ComponentIdeal(fbb)] := Copy(fbb);
  return f;
end intrinsic;

intrinsic HMFZero(Mk::ModFrmHilD :
                  coeff_ring := DefaultCoefficientRing(Mk), prec := Precision(Parent(Mk))
  ) -> ModFrmHilDElt
  {create zero ModHilFrmDElt of weight k.}
  M := Parent(Mk);
  coeffs := AssociativeArray();
  for bb in NarrowClassGroupReps(M) do
    coeffs[bb] := HMFComponentZero(Mk, bb : prec := prec, coeff_ring := coeff_ring);
  end for;
  return HMFSumComponents(Mk, coeffs);
end intrinsic;

intrinsic IsZero(f::ModFrmHilDElt) -> BoolElt
  {check if form is identically zero up to the stored precision}
  return IsZero([f_bb : f_bb in Components(f)]);
end intrinsic;

intrinsic HMFIdentity(Mk::ModFrmHilD :
                      coeff_ring := DefaultCoefficientRing(Mk), prec := Precision(Parent(Mk))) -> ModFrmHilDElt
  {create one ModHilFrmDElt of weight zero and trivial character}
  require &and[w eq 0: w in Weight(Mk)]: "Cannot construct HMF component equal to 1 in nonzero weight";
  M := Parent(Mk);
  C := AssociativeArray();
  for bb in NarrowClassGroupReps(M) do
    C[bb] := HMFComponentIdentity(Mk, bb : coeff_ring := coeff_ring, prec := prec);
  end for;
  return HMFSumComponents(Mk, C);
end intrinsic;

////////////// ModFrmHilDElt: Coercion /////////////////////////

intrinsic ChangeCoefficientRing(f::ModFrmHilDElt, R::Rng) -> ModFrmHilDElt
  {returns f such that a_nu := R!a_nu}
  M := GradedRing(f);
  bbs := NarrowClassGroupReps(M);
  // first make a copy
  f := Copy(f);
  // then change ring
  components := Components(f);
  for bb->fbb in components do
    components[bb] := ChangeRing(components[bb], R);
  end for;
  return HMFSumComponents(Parent(f), components);
end intrinsic;

intrinsic IsCoercible(Mk::ModFrmHilD, f::.) -> BoolElt, .
{}
    if Type(f) eq RngIntElt then
        if f eq 0 then
            return true, HMFZero(Mk);
        else
            return true, f * HMFIdentity(Mk); // throws error if weight is not 0
        end if;
    elif Type(f) eq ModFrmHilDElt then
        if Parent(f) eq Mk then
            return true, f;
        else
            return false, "Not the same parent";
        end if;
    else
        return false, "Not a ModFrmHilDElt";
    end if;
end intrinsic;

intrinsic 'in'(x::., y::ModFrmHilDElt) -> BoolElt
  {}
  return false;
end intrinsic;

intrinsic IsCoercible(x::ModFrmHilDElt, y::.) -> BoolElt, .
  {}
  return false;
end intrinsic;

//////////  ModFrmHilDElt: Galois action on Coefficients //////////

intrinsic MapCoefficients(m::Map, f::ModFrmHilDElt) -> ModFrmHilDElt
  {return the ModFrmHilDElt where the map acts on the coefficients}
  components := Components(f);
  for bb->fbb in components do
    components[bb] := MapCoefficients(m, fbb);
  end for;
  return HMFSumComponents(Parent(f), components);
end intrinsic;

intrinsic GaloisOrbit(f::ModFrmHilDElt) -> SeqEnum[ModFrmHilDElt]
  {returns the full Galois orbit of a modular form}
  k := Weight(f);
  M := GradedRing(f);
  R := CoefficientRing(f);
  require IsNumberField(R) or R eq Rationals(): "Coefficient ring must be a number field";

  G, Pmap, Gmap := AutomorphismGroup(R);
  result := [];
  for g in G do
    Append(~result, MapCoefficients(Gmap(g), f));
  end for;
  return result;
end intrinsic;

intrinsic Trace(f::ModFrmHilDElt) -> ModFrmHilDElt
  {return Trace(f)}
  C := Components(f);
  nC := AssociativeArray();
  for bb in Keys(C) do
    nC[bb] := Trace(C[bb]);
  end for;
  return HMFSumComponents(Parent(f), nC);
end intrinsic;

intrinsic GaloisOrbitDescent(f::ModFrmHilDElt) -> SeqEnum[ModFrmHilDElt]
  {
    Given an HMF element f of a HMFSpace Mk with coefficients in a field L
    containing the default coefficient ring K of Mk, returns a K-basis
    for the subspace of Mk spanned by the Gal(L/K)-conjugates of f. 
  }
  
  K := DefaultCoefficientRing(Parent(f));
  if CoefficientRing(f) eq K then
    return [f];
  elif IsIsomorphic(CoefficientRing(f), K) then
    return [ChangeCoefficientRing(f, K)];
  end if;

  if K eq Rationals() then
    L := CoefficientRing(f);
  else
    L := RelativeField(CoefficientRing(f), K);
  end if;

  result := [Parent(f) | ];
  for b in Basis(L) do
    Append(~result, Trace(b * f));
  end for;
  return result;
end intrinsic;

////////// ModFrmHilDElt: Arithmetic //////////

intrinsic 'eq'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> BoolElt
{compares Parent and Components.}
  return &and[a(f) eq a(g): a in [Parent, Components]];
end intrinsic;

intrinsic 'eq'(f::ModFrmHilDElt, c::RngElt) -> BoolElt
  {compare f against a scalar c}
  return &and[elt eq c : elt in Components(f)];
end intrinsic;

intrinsic 'eq'(c::RngElt, f::ModFrmHilDElt) -> BoolElt
  {compare f against a scalar c}
  return f eq c;
end intrinsic;

intrinsic '*'(c::Any, f::ModFrmHilDElt) -> ModFrmHilDElt
  {return c*f with scalar c}
  new_comp := AssociativeArray();
  comp := Components(f);
  for bb in Keys(comp) do
    new_comp[bb] := c * comp[bb];
  end for;
  return HMFSumComponents(Parent(f), new_comp);
end intrinsic;

intrinsic '*'(f::ModFrmHilDElt, c::Any) -> ModFrmHilDElt
  {scale f by scalar c}
  return c*f;
end intrinsic;

intrinsic '/'(f::ModFrmHilDElt, c::Any) -> ModFrmHilDElt
  {return f/c with scalar c}
  return (1/c)*f;
end intrinsic;

intrinsic '+'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> ModFrmHilDElt
  {return f+g}
  require Parent(f) eq Parent(g): "we only support addition with the same Parent";
  comp_f := Components(f);
  comp_g := Components(g);
  comp := AssociativeArray();
  for bb in Keys(comp_f) do
    comp[bb] := comp_f[bb] + comp_g[bb];
  end for;
  return HMFSumComponents(Parent(f), comp);
end intrinsic;

intrinsic '-'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> ModFrmHilDElt
  {return f-g.}
  return f + (-1)*g;
end intrinsic;

intrinsic '*'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> ModFrmHilDElt
  {return f*g with the same level}
  require GradedRing(f) eq GradedRing(g): "we only support multiplication inside the same graded ring";
  require Level(f) eq Level(g): "we only support multiplication with the same level";
  comp_f := Components(f);
  comp_g := Components(g);
  comp := AssociativeArray();
  for bb in Keys(comp_f) do
    comp[bb] := comp_f[bb] * comp_g[bb];
  end for;
  return HMFSumComponents(Parent(f)*Parent(g), comp);
end intrinsic;

intrinsic '/'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> ModFrmHilDElt
  {return f/g with the same level}
  require GradedRing(f) eq GradedRing(g): "we only support multiplication inside the same graded ring";
  require Level(f) eq Level(g): "we only support multiplication with the same level";
  comp_f := Components(f);
  comp_g := Components(g);
  comp := AssociativeArray();
  for bb in Keys(comp_f) do
    comp[bb] := comp_f[bb] / comp_g[bb];
  end for;
  return HMFSumComponents(Parent(f)/Parent(g), comp);
end intrinsic;

intrinsic Inverse(f::ModFrmHilDElt) -> ModFrmHilDElt
 {return 1/f in case f has weight zero}
 return HMFIdentity(Parent(f))/f;
end intrinsic;

intrinsic '^'(f::ModFrmHilDElt, n::RngIntElt) -> ModFrmHilDElt
  {return f^n}
  comp := AssociativeArray();
  for bb->fbb in Components(f) do
    comp[bb] := fbb^n;
  end for;
  return HMFSumComponents(Parent(f)^n, comp);
end intrinsic;

intrinsic ChangeToCompositumOfCoefficientFields(list::SeqEnum[ModFrmHilDElt]) -> SeqEnum[ModFrmHilDElt]
  {return a sequence of ModFrmHilDElt where the coefficient ring is the compositum of field of all the fraction fields of the coeffient rings}
  require #list ge 1: "first argument must have at least one element";
  differ := false;
  R := CoefficientRing(list[1]);
  if (IsNumberField(R) or R cmpeq Rationals()) and &and[R eq CoefficientRing(f): f in list] then
    return list;
  end if;

  K := NumberField(CoefficientRing(list[1]));
  for f in list do
    if K ne NumberField(CoefficientRing(f)) then
      K := Compositum(K, NumberField(CoefficientRing(f)));
    end if;
  end for;
  return  [ChangeCoefficientRing(f, K) : f in list];
end intrinsic;

////////// ModFrmHilDElt: M_k(N1) -> M_k(N2) //////////

intrinsic Inclusion(f::ModFrmHilDElt, Mk::ModFrmHilD, mm::RngOrdIdl) -> SeqEnum[ModFrmHilDElt]
  {Takes a form f(z) and produces f(mm*z) in the space Mk}

  iotamf := AssociativeArray();

  mminv := mm^-1;
  M := Parent(Mk);
  for bb in Keys(Components(f)) do
    mmbb := NarrowClassRepresentative(M,mm*bb);
    iotamf[mmbb] := Inclusion(Components(f)[bb], Mk, mm);
  end for;
  return HMFSumComponents(Mk, iotamf);
end intrinsic;

intrinsic Inclusion(f::ModFrmHilDElt, Mk::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  {Takes a form f(z) and produces list of all inclusions of f(dd*z) into Mk}
  N1 := Level(Parent(f));
  N2 := Level(Mk);

  return [Inclusion(f, Mk, dd) : dd in Divisors(N2/N1)];
end intrinsic;

////////// ModFrmHilDElt: swap map //////////

function AutomorphismAct(f, sigma)
  // given a component f and sigma an automorphisms of the base field F, returns the component sigma(f)
  M := GradedRing(f);
  Mk := Space(f);
  F := BaseField(M);
  ZF := Integers(F);
  NN := Level(f);
  NNbar := ideal<ZF | [sigma(x) : x in Generators(NN)]>;
  for bb->u in UnitCharacters(Mk) do
    assert u`trivial; // only implemented for trivial unit character
  end for;
  assert NN eq NNbar; // only implemented for Galois stable level
  assert IsTrivial(Character(Mk)); // only implemented for trivial character

  //chibar := ??
  //Mkbar := HMFSpace(M, NNbar, Weight(f), chibar);
  bb := ComponentIdeal(f);
  bbbar := NarrowClassRepresentative(M, ideal<ZF | [sigma(x) : x in Generators(bb)]>);
  coeff := AssociativeArray();
  for nu->c in Coefficients(f) do
    nubar := F!((sigma^(-1))(nu));
    snubar, epsilon := FunDomainRep(M, nubar: CheckComponent := bbbar);
    //coeff[snubar] := Evaluate(UnitCharacter(f), epsilon)*c; // TODO: check the codomain of the unit character. So far, requiring unit char to be trivial so the evaluation is 1
    coeff[snubar] := c;
  end for;
  return HMFComponent(Mk, bbbar, coeff: prec:=Precision(f));
end function;

intrinsic AutomorphismMap(f::ModFrmHilDElt, sigma::Map) -> ModFrmHilDElt
  {given a hilbert modular form f and sigma an automorphisms of the base field F of f, returns the form sigma(f), where sigma permutes the nu_1, nu_2, ..., nu_n}
  M := GradedRing(f);
  Mk := Parent(f);
  F := BaseField(M);
  ZF := Integers(F);
  NN := Level(f);
  NNbar := ideal<ZF | [sigma(x) : x in Generators(NN)]>;
  require NN eq NNbar: "only implemented for Galois stable level";
  require IsTrivial(Character(Mk)): "only implemented for trivial character";

  for bb->u in UnitCharacters(Mk) do
    require u`trivial: "only implemented for trivial unit character";
  end for;
  //new_unitcharacters := AssociativeArray();
  //for bb->c in UnitCharacters(Mk) do
  //  new_unitcharacters[bb] := UnitCharacter(F, [v: v in ValuesOnGens(c)]);
  //end for;
  LandingSpace := HMFSpace(M, NN, Weight(Mk), Character(Mk): unitcharacters:=UnitCharacters(Mk));

  comp := AssociativeArray();
  for k->fbb in Components(f) do
    sfbb := AutomorphismAct(fbb, sigma);
    comp[ComponentIdeal(fbb)] := sfbb;
  end for;
  return HMFSumComponents(LandingSpace, comp);
 end intrinsic;



intrinsic Swap(f::ModFrmHilDElt) -> ModFrmHilDElt
  {given a hilbert modular form f(z_1, z_2), returns the swapped form f(z_2,z_1)}
  M := GradedRing(f);
  F := BaseField(M);
  require Degree(F) eq 2: "only defined for quadratic fields";
  sigma := hom<F -> F| Trace(F.1) - F.1>;
  return AutomorphismMap(f, sigma);
 end intrinsic;



 intrinsic Symmetrize(f::ModFrmHilDElt) -> ModFrmHilDElt
   {given a hilbert modular form f, returns the symmetric form 1/#Aut(F|Q)*sum_(sigma in Aut) sigma(f)}
   M := GradedRing(f);
   F := BaseField(M);
   Mk := Parent(f);
   A:=Automorphisms(F);
   r:=#A;
   g:=Mk!0;
   for sigma in A do
    g+:=AutomorphismMap(f, sigma);
   end for;
   return g;
  end intrinsic;

 intrinsic IsSymmetric(f::ModFrmHilDElt) -> ModFrmHilDElt
   {given a hilbert modular form f, returns if it is invariant under all the automorphisms of its base field F}
   M := GradedRing(f);
   F := BaseField(M);
   A:=Automorphisms(F);
   for sigma in A do
    if not f eq AutomorphismMap(f, sigma) then return false; end if;
   end for;
   return true;
  end intrinsic;

////////// Miscellaneous //////////

intrinsic IncreasePrecisionWithBasis(g::ModFrmHilDElt, basis::SeqEnum[ModFrmHilDElt]) -> ModFrmHilDElt
  {
    inputs:
      g - a ModFrmHilDElt
      basis - A sequence f_1, ..., f_n of ModFrmHilDElts
    returns:
      g with precision equal to the minimum precision of an f_i, if possible.
      Otherwise, returns g as is
  }
  lindep := LinearDependence(basis cat [g]);
  // if the linear dependence of g with the basis is not 1
  // then we cannot use the basis to increase precision
  if #lindep eq 1 then
    lindep := lindep[1];
    g := &+[-1 * lindep[i] * basis[i] / lindep[#basis + 1] : i in [1 .. #basis]];
  end if;
  return g;
end intrinsic;

intrinsic IncreasePrecisionWithBasis(subspace::SeqEnum[ModFrmHilDElt], basis::SeqEnum[ModFrmHilDElt]) -> SeqEnum[ModFrmHilDElt]
  {}
  return [IncreasePrecisionWithBasis(g, basis) : g in subspace];
end intrinsic;

intrinsic Normalize(f::ModFrmHilDElt) -> ModFrmHilDElt
  {}
  coeff_mtrx := CoefficientsMatrix([f]);
  d := Denominator(coeff_mtrx);
  K := CoefficientRing(f);
  return f * K!d;
end intrinsic;
