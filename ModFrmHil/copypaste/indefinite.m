freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Hecke operators with level structure for the indefinite method
// June 2008, Matthew Greenberg
// May 2009, John Voight
//
//////////////////////////////////////////////////////////////////////////////

import "../../Algebra/AlgQuat/enumerate.m" :
             EnumerativeSearchInternal, ReducedBasisInternal;
import "../../Geometry/GrpPSL2/GrpPSL2Shim/domain.m" :
             InternalShimuraInterreduce;
import "../../Algebra/AlgAss/ideals-jv.m" : IsIsomorphicInternal;

import "level.m" : Gamma0Cosets;

declare attributes AlgQuatOrd : ElementOfNormMinusOne;
declare attributes AlgAssVOrd : ElementOfNormMinusOne;
declare attributes GrpPSL2 : ShimGroupSidepairsQuats, ShimGroupFreeAbelianQuotient, HeckeReps;

debug := false;

//-------------
//
// Preliminary functions.
//
//-------------

// returns a unit in O whose norm is negative at the (unique) real place
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

  // Check for cheating.
  for alpha in [B.1, B.2] do
    if not IsTotallyPositive(Norm(alpha)) and IsUnit(Z_F!Norm(alpha)) then
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

function LeftIdealGens(Gamma, ell, Iq, piq, O, Op, iotaell : Slow := false, ALval := false)
  vprintf ModFrmHil: "Principalizing ....................................... ";
  time0 := Cputime();  

  Z_F := BaseRing(O);
  F := NumberField(Z_F);
  B := Algebra(O);
  FeqQ := F cmpeq Rationals();

  _ell := FeqQ select Generator(ell) else ell;

  if assigned Gamma`HeckeReps and Type(ALval) ne RngIntElt then
    for hecke in Gamma`HeckeReps do
      if hecke[1] eq _ell and hecke[2] eq Slow then
        vprintf ModFrmHil: "Time: %o\n", Cputime(time0); 
        return hecke[3];
      end if;
    end for;
  end if;

  assert RightOrder(Iq) eq O;
  assert LeftOrder(Iq) eq Op;
  assert BaseRing(Gamma) eq O;

  Cl, mCl := NarrowClassGroup(Z_F);

  if Type(ALval) eq RngIntElt and Valuation(Discriminant(B), ell) gt 0 then
    I := ideal<O | Generators(CommutatorIdeal(O)) cat Generators(ell)>;
    IqI := Iq*I;

    bl, lambda := IsPrincipal(IqI, Gamma : Strict := true);

    vprintf ModFrmHil: "Time: %o\n", Cputime(time0); 
    return [lambda];
  end if;

  ell := _ell;

  M2Fell, m2Fell, mell := pMatrixRing(O, ell);
  Fell := BaseRing(M2Fell);
  Z_Fell := RingOfIntegers(Fell);
  Nell := Norm(ell);
  unif := UniformizingElement(Z_Fell);

  if not Slow then
    ZbO := ZBasis(O);
    lambdatilde := (M2Fell![0,1,0,0])@@m2Fell;
    c := FeqQ select Eltseq(O!lambdatilde) else Coordinates([lambdatilde], ZbO)[1];
    if &and[IsCoercible(Integers(Nell), c[i]) : i in [1..#ZbO]] then
      lambdatilde := O!&+[ (Integers()!(Integers(Nell)!(c[i])))*ZbO[i] : i in [1..#ZbO]];
    end if;

    assert lambdatilde in O;
    I := lideal<O | [lambdatilde] cat Generators(ell)>;
    IqI := Iq*I;

    bl, lambda := IsPrincipal(IqI, Gamma : Strict := true);
    assert bl; 
    if FeqQ then
      assert Norm(lambda) eq Norm(IqI) and
             IqI eq lideal<LeftOrder(IqI) | lambda>;
    else
      assert Norm(lambda)*Z_F eq Norm(IqI) and
             IqI eq lideal<LeftOrder(IqI) | lambda>;
    end if;
    vprintf ModFrmHil: "Time: %o\n", Cputime(time0); 

    if Type(ALval) ne RngIntElt then
      if assigned Gamma`HeckeReps then
        Append(~Gamma`HeckeReps, [* ell, Slow, lambda *]);
      else
        Gamma`HeckeReps := [ [* ell, Slow, lambda *] ];
      end if;
    end if;
    return lambda;
  else
    k, mk := ResidueClassField(Z_Fell);
    S := [x : x in k];

    P1 := {<a,1> : a in S} join {<1,0>};
    G := {};

    ZbO := ZBasis(O);

    Is := [];
    if Type(ALval) eq RngIntElt then
      lambdatilde := (M2Fell![0,1,unif^ALval,0])@@m2Fell;

      c := FeqQ select Eltseq(O!lambdatilde) else Coordinates([lambdatilde], ZbO)[1];
      assert &and[IsCoercible(Integers(Nell^ALval), c[i]) : i in [1..#ZbO]];
      lambdatilde := O!&+[ (Integers()!(Integers(Nell^ALval)!(c[i])))*ZbO[i] : i in [1..#ZbO]];

      assert lambdatilde in O;
      assert Valuation(m2Fell(lambdatilde)[2,1]) ge ALval;

      I := lideal<O | [lambdatilde] cat Generators(ell^ALval)>;
      IqI := Iq*I;

      Append(~Is, IqI);
    else
      for i := 1 to Norm(ell)+1 do
        if i eq Norm(ell)+1 then
          lambdatilde := (M2Fell![0,1,unif,0])@@m2Fell;
        else
          lambdatilde := (M2Fell![1,S[i]@@mk,0,unif])@@m2Fell;
        end if;
        assert lambdatilde in O;

        c := FeqQ select Eltseq(O!lambdatilde) else Coordinates([lambdatilde], ZbO)[1];
        if &and[IsCoercible(Integers(Nell), c[i]) : i in [1..#ZbO]] then
          lambdatilde := O!&+[ (Integers()!(Integers(Nell)!(c[i])))*ZbO[i] : i in [1..#ZbO]];
        end if;
        I := lideal<O | [lambdatilde] cat Generators(ell)>;
        IqI := Iq*I;

        Append(~Is, IqI);
      end for;
    end if;
  
    lambdas := [];
    for i := 1 to #Is do
      bl, lambda := IsPrincipal(Is[i], Gamma : Strict := true);
      assert bl and Norm(lambda)*Z_F eq Norm(Is[i]) and
           Is[i] eq lideal<LeftOrder(Is[i]) | lambda>;
      lambda := piq*lambda;
      Nlambda := Norm(lambda);
      Append(~lambdas, lambda);
    end for;

    vprintf ModFrmHil: "Time: %o\n", Cputime(time0); 

    if Type(ALval) ne RngIntElt then
      if assigned Gamma`HeckeReps then
        Append(~Gamma`HeckeReps, [* ell, Slow, lambdas *]);
      else
        Gamma`HeckeReps := [ [* ell, Slow, lambdas *] ];
      end if;
    end if;
    return lambdas;
  end if;
end function;

intrinsic ElementOfNorm(O::AlgQuatOrd, p::RngIntElt) -> AlgQuatOrdElt
  {Returns an element of norm p in O, p prime to the discriminant of O.}

  QQ := NumberField(Polynomial([0,1]) : DoLinearExtension := true);
  ZZ := MaximalOrder(QQ);
  a,b := StandardForm(Algebra(O));
  B := QuaternionAlgebra<QQ | a,b>;
  OO := Order([B | Eltseq(x) : x in Basis(O)]);

  xi := ElementOfNorm(OO, ideal<ZZ | p>);
  xi := O!Algebra(O)!Eltseq(xi);
  if Norm(xi) lt 0 then
    xi *:= ElementOfNormMinusOne(O);
  end if;
  return xi;
end intrinsic;

intrinsic ElementOfNorm(O::AlgAssVOrd, p::RngOrdIdl) -> AlgAssVOrdElt
  {Returns an element of norm p in O, p prime to the discriminant of O.}

  Z_F := BaseRing(O);
  require Discriminant(O) + p eq ideal<Z_F | 1>: 
    "p must be prime to the discriminant of O";
  require IsPrime(p) : "p must be prime, for now anyway";

  M2Fp, phiFp := pMatrixRing(O, p);
  nu := M2Fp.1@@phiFp;
  I := rideal<O | [nu] cat Generators(p)>;
  bl, xi := IsPrincipal(I);
  return xi;
end intrinsic;

//-------------
//
// 'All important' solution to the word problem.
//
//-------------

intrinsic RelationFromUnit(Gamma, alpha) -> SeqEnum
  {}

  c := ShimuraReduceUnit(Gamma!alpha)[3];
  // assert IsScalar(Quaternion(c[1]));
  rel := [];
  for i := 1 to #Generators(Group(Gamma)) do
    Append(~rel, + #[j : j in c | j eq i] - #[j : j in c | j eq -i]);
  end for;
  return rel;
end intrinsic;

//-------------
//
// Assisted principalization with fundamental domain.
//
//-------------

intrinsic IsPrincipal(I, Gamma::GrpPSL2 : CheckPrincipal := true, Strict := false) -> BoolElt, AlgQuatElt
  {Determines if the ideal I is principal; uses a combination of lattice reduction and
   reduction utilizing the fundamental domain for the action of Gamma.
   Just search for a generator if CheckPrincipal is set to false.}

  O := Order(I);
  A := Algebra(O);
  F := BaseField(A); 
  Z_F := BaseRing(O);
  FeqQ := F cmpeq Rationals();

  N := Norm(I);
  NN := Norm(N);

  if FeqQ then
    bl := true;
    Nnu := N;
  else
    bl, Nnu := IsPrincipal(N); 
  end if;

  if assigned Gamma`ShimFDDisc then
    D := Parent(Gamma`ShimFDDisc[1]);
  else
    D := UnitDisc();
  end if;
  ZBI := ZBasis(I);

  if FeqQ or not CheckPrincipal then
    Lbasis, L := ReducedBasisInternal(ZBI, A : q0 := D!0);
  else
    if not bl then
      return false, _;  // necessary, but not sufficient condition
    end if;

    if Strict then
      S := RealPlaces(F);
    else
      _, S := RamifiedPlaces(A);
    end if;
    sgnsNnu := RealSigns(Nnu);
    sgns := [sgnsNnu[Index(RealPlaces(F), v)] : v in S];

    u := RealWeakApproximation(S, sgns : UnitOnly);
    if u cmpeq false then
      return false, _;
    end if;
    Nnu *:= u;

    isRight := IsRightIdeal(I);
    w := [1/Abs(Evaluate(Nnu,v)) : v in RealPlaces(F)];

    Lbasis, L := ReducedBasisInternal(ZBI, A : q0 := D!0, w := w);
  end if;

  d := 1;
  dd := Degree(F);
  m := 0;
  SVP := ShortVectorsProcess(L, d);
  while true do
    v := NextVector(SVP);
    if IsZero(v) then
      m +:= 1;
      SVP := ShortVectorsProcess(L, m*d, (m+1)*d);
      continue;
    end if;
    // this is correct, on the assumption that ReducedBasisInternal 
    // constructs a LatticeWithGram, which it does in the Shimura case!
    delta := &+[Round(v[i])*ZBI[i] : i in [1..4*dd]];
    if Abs(Norm(Norm(delta))) eq NN then
      if not Strict or IsTotallyPositive(Norm(delta)) then
        return true, delta;
      end if;
    end if;
  end while;
end intrinsic;
