
////////// ModFrmHilDEltComp attributes //////////

declare type ModFrmHilDEltComp [ModFrmHilDElt];
declare attributes ModFrmHilDEltComp:
  Parent, // ModFrmHilD
  Precision, // RngIntElt
  Coefficients, // Assoc:  coeffs_bb[nu] = a_(bb,nu) = a_(nu bb'^-1),
                // where nu in Shintani cone with Tr(nu) <= Precision
  CoefficientRing, // Rng: where the coefficients live (does this depend on bb?)
  ComponentIdeal; // RngOrdIdl, representative of the narrow class element

/************ ModFrmHilDElt attributes ************/
declare attributes ModFrmHilDElt:
  Parent,
  Components; // Assoc: bb --> f_bb, each f_bb of type ModFrmHilDEltComp



////////// ModFrmHilDEltComp fundamental intrinsics //////////

intrinsic Print(f::ModFrmHilDEltComp, level::MonStgElt : num_coeffs := 10)
  {}
  if level in ["Default", "Minimal", "Maximal"] then
    Mk := Parent(f);
    M := Parent(Mk);
    k := Weight(Mk);
    prec := Precision(f);
    coeffs := Coefficients(f);
    N := Level(Mk);
    if level ne "Minimal" then
      printf "Component of Hilbert modular form expansion with precision %o.\n", prec;
      printf "Parent: %o\n", Mk;
    end if;
    bb := ComponentIdeal(f);
    printf "Coefficients for component ideal class bb = %o\n", bb;
    printf "\n\t(Norm, nu)  |--->   a_nu";
    count := 0;
    for nu in FunDomainRepsUpToNorm(M, bb, prec) do
      t := CorrectNorm(RepToIdeal(M)[bb][nu]);
      printf "\n\t(%o, %o)  |--->   %o", t,  nu, coeffs[nu];
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

intrinsic Print(f::ModFrmHilDElt, level::MonStgElt : num_coeffs := 10)
  {}
  if level in ["Default", "Minimal", "Maximal"] then
    Mk := Parent(f);
    M := Parent(Mk);
    bbs := NarrowClassGroupReps(M);
    k := Weight(Mk);
    N := Level(Mk);
    if level ne "Minimal" then
      printf "Hilbert modular form expansion: ";
      printf "Parent: %o\n", Mk;
    end if;
    for bb in bbs do
      Print(Components(f)[bb], level  : num_coeffs := num_coeffs);
    end for;
  elif level eq "Magma" then
    error "not implemented yet!";
  else
    error "not a valid printing level.";
  end if;
end intrinsic;


////////// ModFrmHilDElt and ModFrmHilDEltComp access to attributes //////////

intrinsic Parent(f::ModFrmHilDEltComp) -> ModFrmHilD
  {returns ModFrmHilD space where f lives.}
  return f`Parent;
end intrinsic;

intrinsic Parent(f::ModFrmHilDElt) -> ModFrmHilD
  {returns ModFrmHilD space where f lives.}
  return f`Parent;
end intrinsic;

intrinsic Precision(f::ModFrmHilDEltComp) -> RngIntElt
  {}
  return f`Precision;
end intrinsic;

intrinsic Weight(f::ModFrmHilDElt) -> SeqEnum[RngIntElt]
  {returns weight of f.}
  return Weight(Parent(f));
end intrinsic;

intrinsic Weight(f::ModFrmHilDEltComp) -> SeqEnum[RngIntElt]
  {returns weight of f.}
  return Weight(Parent(f));
end intrinsic;

intrinsic GradedRing(f::ModFrmHilDEltComp) -> ModFrmHilDGRng
  {return parent of parent of f}
  Mk := Parent(f);
  return Parent(Mk);
end intrinsic;

intrinsic GradedRing(f::ModFrmHilDElt) -> ModFrmHilDGRng
  {return parent of parent of f}
  Mk := Parent(f);
  return Parent(Mk);
end intrinsic;

intrinsic UnitCharacter(f::ModFrmHilDEltComp) -> GrpCharUnitTotElt
  {return the unit character of f}
  return UnitCharacters(Parent(f))[ComponentIdeal(f)];
end intrinsic;




intrinsic BaseField(f::ModFrmHilDEltComp) -> FldNum
  {return base field of parent of f.}
  return BaseField(GradedRing(f));
end intrinsic;

intrinsic BaseField(f::ModFrmHilDElt) -> FldNum
  {return base field of parent of f.}
  return BaseField(GradedRing(f));
end intrinsic;

intrinsic Level(f::ModFrmHilDEltComp) -> RngOrdIdl
  {return level of parent of f.}
  return Level(Parent(f));
end intrinsic;

intrinsic Level(f::ModFrmHilDElt) -> RngOrdIdl
  {return level of parent of f.}
  return Level(Parent(f));
end intrinsic;

intrinsic ComponentIdeal(f::ModFrmHilDEltComp) -> RngOrdIdl
  {return the component of f}
  return f`ComponentIdeal;
end intrinsic;

intrinsic Components(f::ModFrmHilDElt) -> Assoc
  {return the components of f}
  return f`Components;
end intrinsic;

intrinsic Coefficient(f::ModFrmHilDElt, bb::RngOrdIdl, nu::RngElt) -> Any
  {}
  return Coefficients(Components(f)[bb])[nu];
end intrinsic;

intrinsic Coefficient(f::ModFrmHilDEltComp, nu::RngElt) -> Any
  {}
  return Coefficients(f)[nu];
end intrinsic;

intrinsic Coefficient(f::ModFrmHilDElt, nn::RngOrdIdl) -> RngElt
  {}
  require not IsZero(nn) : "The zero coefficient exists on each component";
  M := Parent(Parent(f));
  nu := IdealToRep(M, nn);
  bb := IdealToNarrowClassRep(M, nn);
  return EltCoeffToIdlCoeff(Coefficient(f, bb, nu), nu, f);
end intrinsic;

intrinsic Coefficients(f::ModFrmHilDEltComp) -> Any
  {}
  return f`Coefficients;
end intrinsic;

intrinsic Coefficients(f::ModFrmHilDElt) -> Any
  {}
  coeffs := AssociativeArray();
  for bb in Keys(Components(f)) do
    coeffs[bb] := Coefficients(Components(f)[bb]);
  end for;
  return coeffs;
end intrinsic;

intrinsic IdlCoeffToEltCoeff(a_nn::FldElt, nu::FldElt, k::SeqEnum[RngIntElt], K::Fld) -> FldElt
  {
    inputs:
      a_nn: An element of a number field (usually the splitting field of 
              the base field of the HMF if GaloisDescent has been performed)
              representing the "Frobenius trace" at nn. 
              // TODO abhijitm phrase better, not exactly true
      nu: A totally positive element of a number field (the base field of the HMF)
      k: A weight
      K: The field in which the output should live. Usually this will be
        the coefficient field. 
    returns:
      The Fourier coefficient at nu of the HMF, the coefficient field.

      The coefficients of an HMF are naturally indexed by totally positive elements
      nu. However, after ExtendsMultiplicatively and GaloisDescent, we have coefficients
      indexed by ideals nn. Fix a set of narrow class representatives. Based on the 
      narrow class of nn, there is a narrow class representative bbp such that 
      nn * bbp is a principal ideal. (In our code we
      call this the ideal dual of a narrow class group representative but this distinction
      isn't important here). 

      However, the choice of generator nu such that bbp * nn = (nu) 
      is not canonical, and by the modular transformation law,
      two candidate generators nu and eps * nu -- for some totally positive unit eps -- 
      should have Fourier coefficients related by 

      a_(nu) = \prod_i eps_i^(k_i) a_(eps*nu),

      where eps_i is the image of eps under the ith real embedding. 
      When the weight is parallel (k_1 = ... = k_n) then we have
      a_nu = a_(eps*nu) but in general this is not the case.

      Shimura (Duke 78 Vol 45 No. 3) then writes

      a_(nu) := a_(nn) * N(bbp)^(k_0/2) * nu^((k-k_0)/2)

      where k_0 is the largest entry of k and nu_i is the image of nu under the ith
      real embedding. This definition is compatible with the earlier transformation law.

      This definition is canonical once we fix the normalization of each
      Hecke operator, since we want the a_nn to be eigenvalues. In our case, the normalization
      comes fixed because it comes from the Hecke code in ModFrmHil.

      To reduce the degree of the number fields we need to work with, we use
      the *technically incorrect* formula

      a_(nu) := a_(nn) * nu^((k-k_0)/2)

      Thus, each component will be off by a factor of N(bbp)^(k_0/2). 
      // TODO abhijitm I think this is actually broken... but I also
      // think the existing code should be broken and it doesn't seem
      // to be so idk. 
    }

  if nu eq 0 then
    return StrongCoerce(K, a_nn);
  end if;

  // TODO abhijitm there's some chance that this is wrong
  // the narrow class number is bigger than 1, but I think
  // it's alright... although it might cause problems in 
  // the nonparitious case as written

  return StrongMultiply(K, [* a_nn, EltToShiftedHalfWeight(nu, k)^(-1) *]);
end intrinsic;

intrinsic EltCoeffToIdlCoeff(a_nu::FldElt, nu::FldElt, k::SeqEnum[RngIntElt], K::Fld) -> FldElt
  {
    inputs:
      a_nu: An element of a number field (usually the splitting field 
              of the base field of the HMF if GaloisDescent has been performed)
              representing the Fourier coefficient at nu.
      nu: A totally positive element of a number field (the base field of the HMF)
      k: A weight
      K: The field in which the output should live. Usually this will be
        the coefficient field. 
    returns:
      The "Frobenius trace" at nn of the HMF, the coefficient field.

      Reversing the formula in IdlCoeffToEltCoeff (explanation provided
      in that function), we compute

      a_(nn) := a_(nu) * N(nu)^((k_0-k_i)/2)
  }

  if nu eq 0 then
    return StrongCoerce(K, a_nu);
  end if;

  return StrongMultiply(K, [* a_nu, K!EltToShiftedHalfWeight(nu, k) *]);
end intrinsic;

intrinsic EltCoeffToIdlCoeff(a_nu::FldElt, nu::FldElt, f::ModFrmHilDElt) -> FldElt
  {
    inputs:
      a_nu: An element of a number field (usually the splitting field 
              of the base field of the HMF if GaloisDescent has been performed)
              representing the Fourier coefficient at nu.
      nu: A totally positive element of a number field (the base field of the HMF)
      f: An element of an HMF Space.
    returns:
      The "Frobenius trace" a_nn at the ideal nn corresponding to nu. 
      See the called function for details.
  }
  return EltCoeffToIdlCoeff(a_nu, nu, Weight(Parent(f)), CoefficientRing(f));
end intrinsic;

intrinsic IdlCoeffToEltCoeff(a_nn::FldElt, nu::FldElt, f::ModFrmHilDElt) -> FldElt
  {
    inputs:
      a_nn: An element of a number field (usually the splitting field of 
              the base field of the HMF if GaloisDescent has been performed)
              representing the "Frobenius trace" at nn. 
              // TODO abhijitm phrase better, not exactly true
      nu: A totally positive element of a number field (the base field of the HMF),
        which we expect to be (but do not check) a generator for nn * bbp for some bb.
      f: An element of an HMF Space.
    returns:
      The Fourier coefficient at the totally positive element nu

      See the called function for details.
  }

  return IdlCoeffToEltCoeff(a_nn, nu, Weight(Parent(f)), CoefficientRing(f));
end intrinsic;

intrinsic CoefficientRing(f::ModFrmHilDEltComp) -> Any
  {}
  return f`CoefficientRing;
end intrinsic;

intrinsic CoefficientRing(f::ModFrmHilDElt) -> Any
  {}

  ZF := Integers(GradedRing(f));
  R := CoefficientRing(Components(f)[1*ZF]);
  for bb -> fbb in Components(f) do
    if CoefficientRing(fbb) ne R then
      // check that not a subset
      if R subset CoefficientRing(fbb) then
        R := CoefficientRing(fbb);
      else
        require CoefficientRing(fbb) subset R : "Need all base rings of all components to be equal";
      end if;
    end if;
  end for;
  return R;
end intrinsic;

intrinsic NumberOfCoefficients(f::ModFrmHilDEltComp) -> Any
{}
  return #Coefficients(f);
end intrinsic;

intrinsic NumberOfCoefficients(f::ModFrmHilDElt) -> Any
{}
  return &+[NumberOfCoefficients(fcomp): fcomp in Components(f)];
end intrinsic;


////////// ModFrmHilDElt and ModFrmHilDEltComp creation functions //////////

intrinsic HMFComp(Mk::ModFrmHilD,
                  bb::RngOrdIdl,
                  coeffs::Assoc
                  :
                  coeff_ring := DefaultCoefficientRing(Mk),
                  CoeffsByIdeals := false,
                  prec := 0) -> ModFrmHilDEltComp
  {
    Return the ModFrmHilDEltComp with parent Mk, component ideal bb, the fourier coefficients
    in the Shintani cone, and unit character.
    Explicitly, coeffs is an associative array where
    coeffs[nu] = a_(bb, nu) = a_nn
        where nn = nu*(bb')^-1 and bb' = bb^(-1)*dd_F
    for all nu in the Shintani cone, unless CoeffsByIdeals is true
    (to allow backwards compatibility), in which case
    coeffs[nn] = a_nn as above (and we assign according to Shintani rep).

    The coefficients are assumed to lie in Mk`DefaultCoefficientRing
    unless the optional argument coeff_ring is passed, in which
    case we require that coeff_ring contain Mk`DefaultCoefficientRing
    and that all the input coefficients can be coerced into coeff_ring.
  }
  M := Parent(Mk);
  bbs := NarrowClassGroupReps(M);
  require bb in bbs: "bb should be among the chosen representatives of the narrow class group";

  // make the HMF
  f := New(ModFrmHilDEltComp);

  if prec eq 0 then
    f`Precision := Precision(M);
  else
    require prec gt 0: "prec must be a positive integer";
    f`Precision := prec;
  end if;

  f`Parent := Mk;
  f`ComponentIdeal := bb;

  if CoeffsByIdeals then
    // first convert according to
    // nn = nu*(bb')^-1 where bb' = dd_F*bb^(-1)
    coeffsnu := AssociativeArray();
    for nn->nu in IdealToRep(M)[bb] do // mapping nn->nu, where nu \in bb' = bb*diff^-1
      if IsDefined(coeffs, nn) then
        coeffsnu[nu] := coeffs[nn];
      end if;
    end for;
    coeffs := coeffsnu;  // goodbye old data!
  end if;

  f`Coefficients := AssociativeArray();
  f`CoefficientRing := coeff_ring;

  for nu in FunDomainRepsUpToNorm(M, bb, f`Precision) do
    b, c := IsDefined(coeffs, nu);
    require b : "Coefficients should be defined for each representative in the Shintani cone up to precision";
    // coerce all the coefficents into the coefficient ring
    f`Coefficients[nu] := (f`CoefficientRing)!coeffs[nu];
  end for;
  return f;
end intrinsic;

intrinsic HMFSumComponents(Mk::ModFrmHilD, components::Assoc) -> ModFrmHilDElt
  {
    Return the ModFrmHilDElt with parent Mk and Components components.
  }
  M := Parent(Mk);
  bbs := NarrowClassGroupReps(M);
  require Keys(components) eq SequenceToSet(bbs): "Coefficient array should be indexed by representatives of Narrow class group";
  // make the HMF
  f := New(ModFrmHilDElt);
  f`Parent := Mk;
  f`Components := AssociativeArray();
  for bb in bbs do
    f_bb := components[bb];
    require ComponentIdeal(f_bb) eq bb: "Components mismatch";
    require Type(f_bb) eq ModFrmHilDEltComp: "The values of components need to be ModFrmHilDEltComp";
    require Mk eq Parent(f_bb): "The parents of the components should be all the same";
    f`Components[bb] := Copy(f_bb);
  end for;
  return f;
end intrinsic;

intrinsic HMF(Mk::ModFrmHilD,
              coeffs::Assoc
              :
              CoeffsByIdeals:=false,
              coeff_rings:=false, // Assoc RngFracIdl -> FldNum
              prec := 0) -> ModFrmHilDElt
  {
    Return the ModFrmHilDElt with parent Mk, with the fourier coefficients given via a
    a double associative array coeffs
    and the unit characters are also given via an associative array indexed on the
    narrow class group representatives.
    Explicitly, coeffs is an double associative array
    coeffs[bb][nu] = a_(bb, nu) = a_(nu)*(bb')^-1
    for all nu in the Shintani cone.

    The optional argument coeff_rings is an associative array
    which takes narrow class group reps to the coefficient field
    of their component. 
  }
  M := Parent(Mk);
  bbs := NarrowClassGroupReps(M);
  require Keys(coeffs) eq SequenceToSet(bbs): "Coefficient array should be indexed by representatives of Narrow class group";
  // make the HMF
  f := New(ModFrmHilDElt);
  f`Parent := Mk;
  f`Components := AssociativeArray();

  if prec cmpeq 0 then
    prec := Precision(M);
  end if;
  if Type(prec) eq RngIntElt then
    orig_prec := prec;
    prec := AssociativeArray();
    for bb in bbs do
      prec[bb] := orig_prec;
    end for;
  else
    require Type(prec) eq Assoc: "prec must be either an integer or a AssociativeArray";
  end if;
  require Keys(prec) eq SequenceToSet(bbs): "Unit character array should be indexed by representatives of Narrow class group";


  for bb in bbs do
    coeff_ring := (coeff_rings cmpeq false) select Mk`DefaultCoefficientRing else coeff_rings[bb];
    f`Components[bb] := HMFComp(Mk, bb, coeffs[bb]: CoeffsByIdeals:=CoeffsByIdeals, coeff_ring := coeff_ring, prec:=prec[bb]);
  end for;
  return f;
end intrinsic;

intrinsic HMF(Mk::ModFrmHilD,
              seqcoeffs::SeqEnum,
              nus::SeqEnum,
              bbs::SeqEnum
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
  return HMF(Mk, coeffs);
end intrinsic;

intrinsic HMF(fbb::ModFrmHilDEltComp) -> ModFrmHilDElt
  {f = fbb}
  f := HMFZero(Parent(fbb));
  f`Components[ComponentIdeal(fbb)] := Copy(fbb);
  return f;
end intrinsic;

intrinsic HMFZero(Mk::ModFrmHilD, bb::RngOrdIdl) -> ModFrmHilDEltComp
  {create zero ModFrmHilDEltComp of weight k.}
  M := Parent(Mk);
  coeffs := AssociativeArray();
  for nu in FunDomainReps(M)[bb] do
    coeffs[nu] := 0;
  end for;
  return HMFComp(Mk, bb, coeffs);
end intrinsic;

intrinsic HMFZero(Mk::ModFrmHilD) -> ModFrmHilDElt
  {create zero ModHilFrmDElt of weight k.}
  M := Parent(Mk);
  coeffs := AssociativeArray();
  for bb in NarrowClassGroupReps(M) do
    coeffs[bb] := HMFZero(Mk, bb);
  end for;
  return HMFSumComponents(Mk, coeffs);
end intrinsic;

intrinsic IsZero(f::ModFrmHilDEltComp) -> BoolElt
  {check if form is identically zero}
  return IsZero([c : c in Coefficients(f)]);
end intrinsic;

intrinsic IsZero(f::ModFrmHilDElt) -> BoolElt
  {check if form is identically zero}
  return IsZero([f_bb : f_bb in Components(f)]);
end intrinsic;

intrinsic HMFIdentity(Mk::ModFrmHilD, bb::RngOrdIdl) -> ModFrmHilDEltComp
  {create one ModHilFrmDElt of weight zero and trivial character}
  M := Parent(Mk);
  N := Level(Mk);
  X := HeckeCharacterGroup(N, [1..Degree(BaseField(M))]);
  chi := X!1;
  k := [0 : i in Weight(Mk)];
  M0 := HMFSpace(M, N, k, chi);
  coeffs := AssociativeArray();
  for nu in FunDomainReps(M)[bb] do
    if IsZero(nu) then
      coeffs[nu] := 1;
    else
      coeffs[nu] := 0;
    end if;
  end for;
  return HMFComp(M0, bb, coeffs);
end intrinsic;

intrinsic HMFIdentity(Mk::ModFrmHilD) -> ModFrmHilDElt
  {create one ModHilFrmDElt of weight zero and trivial character}
  M := Parent(Mk);
  C := AssociativeArray();
  for bb in NarrowClassGroupReps(M) do
    C[bb] := HMFIdentity(Mk, bb);
  end for;
  M0 := Parent(C[1*Integers(M)]);
  return HMFSumComponents(M0, C);
end intrinsic;

////////////// ModFrmHilDElt: Coercion /////////////////////////

//FIXME: this does nto agree with MAGMA standards
// also we need to define ChangeRing
// Coerces HMF coefficients a_n in a ring R
intrinsic ChangeCoefficientRing(f::ModFrmHilDEltComp, R::Rng) -> ModFrmHilDEltComp
  {returns f such that a_nu := R!a_nu}
  bb := ComponentIdeal(f);
  coeffs := Coefficients(f);
  new_coeffs := AssociativeArray(Universe(coeffs));
  for nu->anu in coeffs do
    new_coeffs[nu] := StrongCoerce(R, anu);
  end for;
  return HMFComp(Parent(f), bb, new_coeffs: coeff_ring := R, prec:=Precision(f));
end intrinsic;


intrinsic ChangeCoefficientRing(f::ModFrmHilDElt, R::Rng) -> ModFrmHilDElt
  {returns f such that a_nu := R!a_nu}
  M := GradedRing(f);
  bbs := NarrowClassGroupReps(M);
  // first make a copy
  f := Copy(f);
  // then change ring
  components := Components(f);
  for bb->fbb in components do
    components[bb] := ChangeCoefficientRing(fbb, R);
  end for;
  return HMFSumComponents(Parent(f), components);
end intrinsic;

intrinsic IsCoercible(Mk::ModFrmHilD, f::.) -> BoolElt, .
  {}
  if Type(f) eq RngIntElt and IsZero(f) then
    return true, HMFZero(Mk);
  elif Type(f) notin [ModFrmHilDElt] then
    return false, "f not of type ModFrmHilDElt";
  else // f is an HMF so has a chance to be coercible
    M := Parent(Mk); // graded ring associated to Mk
    Mkf := Parent(f); // space of HMFs associated to f
    Mf := Parent(Mkf); // graded ring associated to f
    if M ne Mf then
      return false, "f does not belong to the same graded ring as Mk";
    else // at least the graded rings match up
      test1 := Weight(Mk) eq Weight(Mkf);
      test2 := Level(Mk) eq Level(Mkf);
      test3 := Character(Mk) eq Character(Mkf);
      test4 := UnitCharacters(Mk) eq UnitCharacters(Mkf);
      if test1 and test2 and test3 and test4 then // all tests must be true to coerce
        components := AssociativeArray();
        for bb in Keys(Components(f)) do
          fbb := Components(f)[bb];
          components[bb] := HMFComp(Mk, bb, Coefficients(fbb): prec:=Precision(fbb));
        end for;
        return true, HMFSumComponents(Mk, components);
      else
        return false, "I tried and failed to coerce";
      end if;
    end if;
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

intrinsic MapCoefficients(m::Map, f::ModFrmHilDEltComp) -> ModFrmHilDEltComp
  {return the ModFrmHilDEltComp where the map acts on the coefficients}
  coeffs := Coefficients(f);
  new_coeffs := AssociativeArray();
  for nu -> anu in coeffs do
    new_coeffs[nu] := m(anu);
  end for;
  return HMFComp(Parent(f), ComponentIdeal(f), new_coeffs : prec:=Precision(f));
end intrinsic;

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
  if IsField(R) then
    K := R;
  else
    K := NumberField(R);
    f := K!f; // HERE
  end if;
  G, Pmap, Gmap := AutomorphismGroup(K);
  result := [];
  for g in G do
    if K eq R then
      Append(~result, MapCoefficients(Gmap(g), f));
    else
      Append(~result, ChangeCoefficientRing(MapCoefficients(Gmap(g), f), R));
    end if;
  end for;
  return result;
end intrinsic;

intrinsic Trace(f::ModFrmHilDEltComp) -> ModFrmHilDEltComp
  {return Trace(f)}
  K := DefaultCoefficientRing(Parent(f));
  new_coeffs := AssociativeArray(Universe(Coefficients(f)));
  for nu->anu in Coefficients(f) do
    new_coeffs[nu] := (K eq Rationals()) select Trace(anu) else Trace(StrongCoerce(K, anu), K);
  end for;
  return HMFComp(Parent(f), ComponentIdeal(f), new_coeffs : coeff_ring := K, prec:=Precision(f));
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
  
  if CoefficientRing(f) eq DefaultCoefficientRing(Parent(f)) then
    return [f];
  end if;

  if DefaultCoefficientRing(Parent(f)) eq Rationals() then
    L := CoefficientRing(f);
  else
    L := RelativeField(CoefficientRing(f), DefaultCoefficientRing(Parent(f)));
  end if;

  result := [Parent(f) | ];
  for b in Basis(L) do
    Append(~result, Trace(b * f));
  end for;
  return result;
end intrinsic;

////////// ModFrmHilDElt: Arithmetic //////////

intrinsic 'eq'(f::ModFrmHilDEltComp, g::ModFrmHilDEltComp) -> BoolElt
{compares Parent, Weight, Component, Precision, UnitCharacter, and Coefficients.}
  if not &and[a(f) eq a(g): a in [Parent, ComponentIdeal, UnitCharacter, Precision]] then
    return false;
  end if;
  if Keys(Coefficients(f)) ne Keys(Coefficients(g)) then
    return false;
  end if;
  for nu in Keys(Coefficients(f)) do
   if Coefficients(f)[nu] ne Coefficients(g)[nu] then
     return false;
   end if;
  end for;
  return true;
end intrinsic;

intrinsic 'eq'(f::ModFrmHilDElt, g::ModFrmHilDElt) -> BoolElt
{compares Parent and Components.}
  return &and[a(f) eq a(g): a in [Parent, Components]];
end intrinsic;

intrinsic 'eq'(f::ModFrmHilDEltComp, c::RngElt) -> BoolElt
  {compare f against a scalar c}
  if Coefficients(f)[0] ne c then
    return false;
  end if;
  return IsZero([Coefficients(f)[nu] : nu in Keys(Coefficients(f)) | nu ne 0]);
end intrinsic;

intrinsic 'eq'(f::ModFrmHilDElt, c::RngElt) -> BoolElt
  {compare f against a scalar c}
  return &and[elt eq c : elt in Components(f)];
end intrinsic;

intrinsic 'eq'(c::RngElt, f::ModFrmHilDEltComp) -> BoolElt
  {compare f against a scalar c}
  return f eq c;
end intrinsic;

intrinsic 'eq'(c::RngElt, f::ModFrmHilDElt) -> BoolElt
  {compare f against a scalar c}
  return f eq c;
end intrinsic;



intrinsic '*'(c::Any, f::ModFrmHilDEltComp) -> ModFrmHilDEltComp
  {scale f by a scalar c.}
  require IsCoercible(CoefficientRing(f), c): "the scalar must be coercible into the base ring";
  F := CoefficientRing(f);
  new_coeffs := AssociativeArray();
  coeffs := Coefficients(f);
  for nu in Keys(coeffs) do
    coeffs[nu] := StrongCoerce(F, c) * coeffs[nu];
  end for;
  return HMFComp(Parent(f), ComponentIdeal(f), coeffs: coeff_ring := F, prec:=Precision(f));
end intrinsic;

intrinsic '*'(f::ModFrmHilDEltComp, c::Any) -> ModFrmHilDEltComp
  {return c*f with scalar c}
  return c*f;
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

intrinsic '/'(f::ModFrmHilDEltComp, c::Any) -> ModFrmHilDEltComp
  {return f/c with a scalar c.}
  return (1/c)*f;
end intrinsic;

intrinsic '/'(f::ModFrmHilDElt, c::Any) -> ModFrmHilDElt
  {return f/c with scalar c}
  return (1/c)*f;
end intrinsic;

intrinsic '+'(f::ModFrmHilDEltComp, g::ModFrmHilDEltComp) -> ModFrmHilDEltComp
  {return f+g with the same parent}
  require Parent(f) eq Parent(g): "we only support addition with the same Parent";
  require ComponentIdeal(f) eq ComponentIdeal(g): "we only support multiplication with the same component";
  require UnitCharacter(f) eq UnitCharacter(g): "we only support addition with the same unit character";
  // update precision to be the minimum of the two precisions?
  prec_f := Precision(f);
  prec_g := Precision(g);
  prec := Minimum(prec_f, prec_g);
  coeffs_f := Coefficients(f);
  coeffs_g := Coefficients(g);

  Ff := CoefficientRing(f);
  Fg := CoefficientRing(g);
  require Ff eq Fg : "We only support addition of HMFs with the same coefficient ring";

  coeffs_h := AssociativeArray(); // h := f+g
  for nu in FunDomainRepsUpToNorm(GradedRing(f), ComponentIdeal(f), prec) do
    coeffs_h[nu] := coeffs_f[nu] + coeffs_g[nu];
  end for;
  return HMFComp(Parent(f), ComponentIdeal(f), coeffs_h : coeff_ring := Ff, prec:=prec);
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

intrinsic '*'(f::ModFrmHilDEltComp, g::ModFrmHilDEltComp) -> ModFrmHilDEltComp
  {return f*g with the same level}
  require GradedRing(f) eq GradedRing(g): "we only support multiplication inside the same graded ring";
  require Level(f) eq Level(g): "we only support multiplication with the same level";
  require ComponentIdeal(f) eq ComponentIdeal(g): "we only support multiplication with the same component";

  char_f := UnitCharacter(f);
  char_g := UnitCharacter(g);

  coeffs_f := Coefficients(f);
  coeffs_g := Coefficients(g);
  coeffs_h := AssociativeArray(); // h := f*g
  
  LandingSpace := Parent(f) * Parent(g);

  Ff := CoefficientRing(f);
  Fg := CoefficientRing(g);
  if Ff eq Fg then
    F := Ff;
  else
    F := Compositum(NumberField(Ff), NumberField(Fg));
    // We try to put things in their default coefficient rings
    // wherever possible
    K := DefaultCoefficientRing(LandingSpace);
    if IsSubfield(F, K) then
      F := K;
    end if;
  end if;

  table := MPairs(GradedRing(f))[ComponentIdeal(f)];

  // TODO: improve precision?
  // use relative precision to gain something here instead of minimum?
  prec_f := Precision(f);
  prec_g := Precision(g);
  prec := Minimum(prec_f, prec_g);

  M := Parent(Parent(f));
  evaluate_bool := not IsOne(char_f) or not IsOne(char_g);
  for nu in FunDomainRepsUpToNorm(GradedRing(f), ComponentIdeal(f), prec) do
    c := F!0;
    for pair in table[nu] do // [[<s(mu1), epsilon1>, <s(mu2), epsilon2>] :  mu = epsilon s(mu), mu' = epsilon' s(mu'), mu + mu' = nu]
      xpair, ypair := Explode(pair); // pair := [<s(mu1), epsilon1>, <s(mu2), epsilon2>]
      smu1, epsilon1 := Explode(xpair); // <s(mu1), epsilon1>
      smu2, epsilon2 := Explode(ypair); // <s(mu2), epsilon2>
      if evaluate_bool then
        c +:= StrongMultiply(F, [* Evaluate(char_f, epsilon1), coeffs_f[smu1], Evaluate(char_g, epsilon2), coeffs_g[smu2] *]);
      else
        c +:= StrongMultiply(F, [* coeffs_f[smu1], coeffs_g[smu2] *]);
      end if;
    end for;
    coeffs_h[nu] := c;
  end for;
  return HMFComp(Parent(f)*Parent(g), ComponentIdeal(f), coeffs_h : coeff_ring := F, prec:=prec);
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


intrinsic '/'(f::ModFrmHilDEltComp, g::ModFrmHilDEltComp) -> ModFrmHilDEltComp
  {return f/g with the same level}
  require GradedRing(f) eq GradedRing(g): "we only support division inside the same graded ring";
  require Level(f) eq Level(g): "we only support division with the same level";
  require ComponentIdeal(f) eq ComponentIdeal(g): "we only support division with the same component";

  LandingSpace := Parent(f)/Parent(g);
  char_g := UnitCharacter(g);
  char_h := UnitCharacters(LandingSpace)[ComponentIdeal(f)];

  coeffs_f := Coefficients(f);
  coeffs_g := Coefficients(g);
  coeffs_h := AssociativeArray(); // h := f/g
                                  
  Ff := CoefficientRing(f);
  Fg := CoefficientRing(g);
  if Ff eq Fg then
    F := Ff;
  else
    F := Compositum(NumberField(Ff), NumberField(Fg));
    // We try to put elements in the default coefficient rings 
    // of their spaces wherever possible
    K := DefaultCoefficientRing(LandingSpace);
    if IsSubfield(F, K) then
      F := K;
    end if;
  end if;

  table := MPairs(GradedRing(f))[ComponentIdeal(f)];

  // TODO: improve precision?
  // use relative precision to gain something here instead of minimum?
  prec_f := Precision(f);
  prec_g := Precision(g);
  prec := Minimum(prec_f, prec_g);

  evaluate_bool := not IsOne(char_g) or not IsOne(char_h);

  for nu in FunDomainRepsUpToNorm(GradedRing(f), ComponentIdeal(f), prec)  do
    sum := F!0; // will record sum_{mu + mu' = nu, mu != 0} a(g)_mu a(h)_mu'
    count := 0;
    for pair in table[nu] do // [[<s(mu1), epsilon1>, <s(mu2), epsilon2>] :  mu = epsilon s(mu), mu' = epsilon' s(mu'), mu + mu' = nu]
      xpair, ypair := Explode(pair); // pair := [<s(mu1), epsilon1>, <s(mu2), epsilon2>]
      smu1, epsilon1 := Explode(xpair); // <s(mu1), epsilon1>
      smu2, epsilon2 := Explode(ypair); // <s(mu2), epsilon2>
      if IsZero(smu1) then // smu1 = 0 => => mu1 = 0 => s(mu2) = mu2 = nu
        //FIXME: these asserts should be moved to the creation of MPairs
        assert smu2 eq nu;
        assert IsOne(epsilon1);
        assert IsOne(epsilon2);
        count +:= 1;
      else
        if evaluate_bool then
          sum +:= StrongMultiply(F, [* Evaluate(char_g, epsilon1), coeffs_g[smu1], Evaluate(char_h, epsilon2), F!coeffs_h[smu2] *]);
        else
          sum +:= StrongMultiply(F, [* coeffs_g[smu1],  F!coeffs_h[smu2] *]);
        end if;
      end if;
    end for;
    //FIXME: this asserts should be moved to the creation of MPairs
    assert count eq 1;
    coeffs_h[nu] := (StrongCoerce(F, coeffs_f[nu]) - sum)/StrongCoerce(F, coeffs_g[0]);
  end for;

  return HMFComp(LandingSpace, ComponentIdeal(f), coeffs_h : coeff_ring := F, prec:=prec);
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

intrinsic Inverse(f::ModFrmHilDEltComp) -> ModFrmHilDEltComp
 {return 1/f}
 return HMFIdentity(Parent(f), ComponentIdeal(f))/f;
end intrinsic;

intrinsic Inverse(f::ModFrmHilDElt) -> ModFrmHilDElt
 {return 1/f}
 return HMFIdentity(Parent(f))/f;
end intrinsic;

intrinsic '^'(f::ModFrmHilDEltComp, n::RngIntElt) -> ModFrmHilDEltComp
  {return f^n}
  if n lt 0 then
    f := Inverse(f);
    n := -n;
  end if;
  g := HMFIdentity(Parent(f), ComponentIdeal(f));
  if n eq 0 then
    return g;
  end if;
  if n eq 1 then
   return f;
   end if;
  while n gt 1 do
    if n mod 2 eq 0 then
      f := f * f;
      n := Integers() ! (n/2);
    else
      g := f * g;
      f := f * f;
      n := Integers() ! ((n - 1)/2);
    end if;
  end while;
  return f * g;
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
  for f in list[2..#list] do
    if R ne CoefficientRing(f) then
      differ := true;
      break;
    end if;
  end for;
  if not differ then
    return list;
  end if;
  K := NumberField(CoefficientRing(list[1]));
  differ := false;
  for f in list do
    if K ne NumberField(CoefficientRing(f)) then
      K := Compositum(K, NumberField(CoefficientRing(f)));
      differ := true;
    end if;
  end for;
  if differ then
    list :=  [ChangeCoefficientRing(f, K) : f in list];
  end if;
  return list;
end intrinsic;



////////// ModFrmHilDElt: M_k(N1) -> M_k(N2) //////////

intrinsic Inclusion(f::ModFrmHilDEltComp, Mk::ModFrmHilD, mm::RngOrdIdl) -> SeqEnum[ModFrmHilDEltComp]
  {Takes a form f(z) and produces f(mm*z) in Mk (of level NN) with component ideal class [mm*bb]}

  coeff_f := Coefficients(f);
  Mk_f := Parent(f);
  M_f := Parent(Mk_f);
  M := Parent(Mk);
  N1 := Level(Mk_f);
  N2 := Level(Mk);
  chi := Character(Mk);
  chif := Character(Mk_f);
  mf, pf := Modulus(chif);
  ZF := Integers(M);
  coeff_ring := f`CoefficientRing;

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

  return HMFComp(Mk, mmbb, coeff : coeff_ring := coeff_ring, prec:=Precision(f));
end intrinsic;

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
  Mk := Parent(f);
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
    snubar, epsilon := FunDomainRep(M, bbbar, nubar);
    //coeff[snubar] := Evaluate(UnitCharacter(f), epsilon)*c; // TODO: check the codomain of the unit character. So far, requiring unit char to be trivial so the evaluation is 1
    coeff[snubar] := c;
  end for;
  return HMFComp(Mk, bbbar, coeff: prec:=Precision(f));
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

