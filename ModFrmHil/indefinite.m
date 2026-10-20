freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Local overrides of functions from Magma's
// !Geometry/ModFrmHil/indefinite.m.
//
// Only the functions we need to change are copied here (the rest are still
// imported from the Magma package); callers import these versions instead. This
// is a stopgap until the fixes are upstreamed to the Magma core repository.
//
//////////////////////////////////////////////////////////////////////////////

declare attributes AlgQuatOrd : ElementOfNormMinusOne;
declare attributes AlgAssVOrd : ElementOfNormMinusOne;

// Returns an element of O whose reduced norm is a unit that is negative at the
// (unique) split real place, i.e. the element inducing the plus-involution at
// infinity.
//
// This is Magma's ElementOfNormMinusOne with one fix: the "check for cheating"
// shortcut below returned a standard algebra generator B.1/B.2 as soon as its
// norm was a non-totally-positive unit, WITHOUT checking that the generator is
// actually in O. For narrow class number > 1 the left order of a non-principal
// class is built with randomness, so B.1/B.2 is often not in O, and returning it
// breaks the "in O" requirement at the call site. We now require the generator
// to be in O before taking the shortcut; otherwise we fall through to the
// short-vector search over ZBasis(O), whose result is in O by construction.
function ElementOfNormMinusOne(O) // AlgAssVOrd) -> AlgAssVOrdElt
  B := Algebra(O);
  F := BaseField(B);
  Z_F := MaximalOrder(F);

  if assigned O`ElementOfNormMinusOne then
    return O`ElementOfNormMinusOne;
  end if;

  if ISA(Type(O), AlgQuatOrd) then
    QQ := NumberField(Polynomial([0,1]) : DoLinearExtension := true);
    ZZ := MaximalOrder(QQ);
    a,b := StandardForm(Algebra(O));
    B := QuaternionAlgebra<QQ | a,b>;
    OO := Order([B | Eltseq(x) : x in Basis(O)]);

    xi := ElementOfNormMinusOne(OO);
    xi := O!Algebra(O)!Eltseq(xi);
    O`ElementOfNormMinusOne := xi;
    return xi;
  end if;

  // Check if one even exists--otherwise, return an element
  // with negative norm.
  U_F, mU := UnitGroup(Z_F);
  vneg := [1 : i in [1..Degree(F)]];
  vneg[Index(RealPlaces(F), SplitRealPlace(B))] := -1;
  u := RealWeakApproximation(RealPlaces(F), vneg : UnitOnly := true);
  if Type(u) eq BoolElt and not u then
    // No such unit exists, so just return a standard generator.
    for alpha0 in [B.1, B.2, B.1+B.2] do
      alpha := alpha0;
      if not IsTotallyPositive(Norm(alpha)) then
        O`ElementOfNormMinusOne := alpha;
        return alpha;
      end if;
    end for;
    error "Serious problem: Both standard generators of the algebra are totally positive";
  end if;

  // Check for cheating (only valid when the generator actually lies in O).
  for alpha in [B.1, B.2] do
    if alpha in O and not IsTotallyPositive(Norm(alpha)) and IsUnit(Z_F!Norm(alpha)) then
      O`ElementOfNormMinusOne := alpha;
      return alpha;
    end if;
  end for;

  d := Degree(F);

  if assigned O`FuchsianGroup and assigned O`FuchsianGroup`ShimWeight then
    w := O`FuchsianGroup`ShimWeight;
  else
    Gamma := FuchsianGroup(O);
    if d eq 1 then
      w := [1];
    else
      w := [];
      for v in RealPlaces(F) do
        if v eq SplitRealPlace(B) then
          Append(~w, (4*Discriminant(Z_F)^(1/d)*ArithmeticVolume(Gamma))^(-1));
        else
          Append(~w, 1.0);
        end if;
      end for;
    end if;
    Gamma`ShimWeight := w;
  end if;

  ZBO := ZBasis(O);
  M := DefiniteGramMatrix(ZBO : w := w);
  L, T := LLL(LatticeWithGram(M));

  det := 1;
  m := 0;
  SVP := ShortVectorsProcess(L, det);
  found := false;
  counter := 0;
  while not found do
    counter +:= 1;
    if counter mod 100 eq 0 then
      vprintf ModFrmHil, 2: "%o tries, ", counter;
    end if;

    v := NextVector(SVP);
    if IsZero(v) then
      m +:= 1;
      SVP := ShortVectorsProcess(L, m*det, (m+1)*det);
      continue;
    end if;
    xi := &+[Round(v[i])*ZBO[i] : i in [1..4*d]];
    Nxi := Norm(xi);
    if Abs(Norm(Nxi)) eq 1 and not IsTotallyPositive(Nxi) then
      found := true;
    end if;
  end while;

  O`ElementOfNormMinusOne := xi;
  return xi;
end function;
