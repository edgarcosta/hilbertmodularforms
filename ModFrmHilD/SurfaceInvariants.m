intrinsic EllipticPointResolution(order::RngIntElt, rot_factor::RngIntElt) ->
	  SeqEnum[RngIntElt], SeqEnum[FldRatElt], SeqEnum[FldRatElt]
{Given the order and rotation factor of an elliptic point, returns the type (n; a, b).}

  frac := order/rot_factor;
  c := [Ceiling(frac)];
  x := [1, frac^(-1)];
  y := [0, order^(-1)];
  Append(~x, c[1]*x[2] - x[1]);
  Append(~y, c[1]*y[2] - y[1]);
  d := c[#c] - frac;
  while (d ne 0) do
      Append(~c, Ceiling(d^(-1)));
      Append(~x, c[#c]*x[#c+1] - x[#c]);
      Append(~y, c[#c]*y[#c+1] - y[#c]);
      d := c[#c] - d^(-1);
  end while;
  return c, x, y;
end intrinsic;

intrinsic EllipticPointK2E(order::RngIntElt, rot_factor::RngIntElt) -> FldRatElt, RngIntElt
{Given the order and rotation factor of an elliptic point, returns the local Chern cycle.}
  c,x,y := EllipticPointResolution(order, rot_factor);
  a := [x[i]+y[i]-1 : i in [2..#c+1]];
  sq := -(&+[a[i]^2*c[i] : i in [1..#c]]);
  k2 := sq + 2*&+[Rationals() | a[i]*a[i+1] : i in [1..#c-1]];

  return k2, #c;
end intrinsic;

intrinsic EulerNumber(Gamma::GrpHilbert) -> RngIntElt
{Given a congruence subgroup, computes the EulerNumber of the resulting Hilbert modular surface.}
  if assigned Gamma`EulerNumber then return Gamma`EulerNumber; end if;

  // for these fields there are additional orders of points
  // At the moment we do not handle them.
  F := BaseField(Gamma);
  ZF := Integers(F);
  D := Discriminant(ZF);

  // require D notin [8,12]: "Discriminant not supported";
  // require (Level(Gamma) eq 1*ZF) or (GCD(Level(Gamma), 3*D*ZF) eq 1*ZF):
  //"Level is not supported";

  cusps := CuspsWithResolution(Gamma);
  vol := VolumeOfFundamentalDomain(Gamma);

  // get cusp contribution
  l := 0;
  for cusp in cusps do
    _, _, L, n := Explode(cusp);
    l +:= #L * n;
  end for;

  // get elliptic points contribution
  a := CountEllipticPoints(Gamma);

  elliptic := 0;
  for rot_factor in Keys(a) do
    rot_tup := IntegerTuple(rot_factor);
    n := rot_tup[1];

    _, len := EllipticPointK2E(n, rot_tup[3]);
    // This is ad-hoc check for surfaces
    if rot_tup[3] eq 1 then
      // len := 1;
      assert len eq 1;
    elif rot_tup[3] eq n-1 then
      // len := n-1;
      assert len eq n-1;
    elif n eq 5 then
      assert rot_tup[3] in [2,3];
      // len := 2;
      assert len eq 2;
    elif n eq 12 then
      if rot_tup[3] eq 5 then
        // len := 3;
        assert len eq 3;
      end if;
    end if;
    elliptic +:= a[rot_tup] * (len + (n-1)/n);
  end for;

  // elliptic := a2 * (1 + 1/2) + a3_plus * (1 + 2/3) + a3_minus * (2 + 2/3);
  e := vol + l + elliptic;
  assert IsIntegral(e);
  Gamma`EulerNumber := Integers()!e;

  return Gamma`EulerNumber;
end intrinsic;

intrinsic K2(Gamma::GrpHilbert) -> RngIntElt
{Given a congruence subgroup, computes the K2 of the resulting Hilbert modular surface.}
  if not assigned Gamma`K2 then
  // for these fields there are additional orders of points
  // At the moment we do not handle them.
  F := BaseField(Gamma);
  ZF := Integers(F);
  D := Discriminant(ZF);

  cusps := CuspsWithResolution(Gamma);
  vol := VolumeOfFundamentalDomain(Gamma);
  // get cusp contribution
  cusp_chern := 0;
  for cusp in cusps do
    _, _, L, n := Explode(cusp);
      if (n eq 1) and (#L eq 1) then
          cusp_chern +:= L[1];
      else
          cusp_chern +:= n*(&+[2+b : b in L]);
      end if;
  end for;

  // get elliptic points contribution
  a := CountEllipticPoints(Gamma);

  elliptic := 0;
  for rot_factor in Keys(a) do
    rot_tup := IntegerTuple(rot_factor);
    n := rot_tup[1];
    k2_pt, _ := EllipticPointK2E(n, rot_tup[3]);

    // verification
    if n eq 5 then
      if rot_tup[3] in [2,3] then
        assert k2_pt eq -2/5;
      elif rot_tup[3] eq 4 then
        assert k2_pt eq 0;
      end if;
    elif n eq 3 then
      if rot_tup[3] eq 1 then
        assert k2_pt eq -1/3;
      else
        assert k2_pt eq 0;
      end if;
    elif n eq 2 then
      assert k2_pt eq 0;
    end if;
    elliptic +:= k2_pt * a[rot_factor];
  end for;

  k2 := 2*vol + cusp_chern + elliptic;
  assert IsIntegral(k2);
  Gamma`K2 := Integers()!k2;
  end if;
  return Gamma`K2;
end intrinsic;

intrinsic ChernNumbersOfMinimalResolution(Gamma::GrpHilbert) -> SeqEnum
{Returns `c1^2, c2`,  corresponding to the Chern numbers of the
minimal resolution of the Hilbert Modular Surface for the Hilbert Modular Group.}
    return ChernNumbers(Gamma);
end intrinsic;

intrinsic ChernNumbers(Gamma::GrpHilbert) -> SeqEnum
{Returns `c1^2, c2`,  corresponding to the Chern numbers of the
minimal resolution of the Hilbert Modular Surface for the Hilbert Modular Group.}
    return K2(Gamma), EulerNumber(Gamma);
end intrinsic;

intrinsic ArithmeticGenus(Gamma::GrpHilbert) -> RngIntElt
{Given a congruence subgroup, computes the Arithmetic Genus of the resulting Hilbert modular
surface.}
  chi := K2(Gamma) + EulerNumber(Gamma);
  assert chi mod 12 eq 0;
  return chi div 12;
end intrinsic;

intrinsic Irregularity(Gamma::GrpHilbert) -> RngIntElt
{Given a congruence subgroup, computes the irregularity of the resulting Hilbert modular surface.
 It is always 0.}
  return 0;
end intrinsic;

intrinsic GeometricGenus(Gamma::GrpHilbert) -> RngIntElt
{Given a congruence subgroup, computes the Geometric Genus of the resulting Hilbert modular
surface.}
  return ArithmeticGenus(Gamma)-1;
end intrinsic;

intrinsic HodgeDiamond(Gamma::GrpHilbert) -> RngIntElt
{Given a congruence subgroup, computes the Hodge Diamond of the resulting Hilbert modular
surface.}
  h_0 := [1];
  q := Irregularity(Gamma);
  h_1 := [q,q];
  p_g := GeometricGenus(Gamma);
  chi := ArithmeticGenus(Gamma);
  e := EulerNumber(Gamma);
  h_2 := [p_g, e - 2*chi, p_g];
  h_3 := h_1;
  h_4 := h_0;
  return [h_0, h_1, h_2, h_3, h_4];
end intrinsic;

intrinsic TestArithmeticGenus(F::FldNum, NN::RngOrdIdl) -> Any
  {Compute the arithmetic genus as (1/12)*(K^2 + e), summed over all components, and as
  dim(S_2) + #Cl^+(F); return true if these are equal. Currently only for GL+ type.}

  NCl, mp := NarrowClassGroup(F);
  chi1 := 0;
  for bb in [mp(el) : el in NCl] do
    G := CongruenceSubgroup("GL+", "Gamma0", F, NN, bb);
    chi1 +:= ArithmeticGenus(G);
    vprintf HilbertModularForms: "for bb = (%o), chi = %o\n",
                                 IdealOneLine(bb), ArithmeticGenus(G);
  end for;
  vprintf HilbertModularForms: "(1/12)*(K^2 + e) = %o\n", chi1;

  M := GradedRingOfHMFs(F, 0);
  h := HilbertSeriesCusp(M, NN);
  //h := HilbertSeriesCusp(G);
  Pow<x> := PowerSeriesRing(Rationals());
  chi2 := Coefficient(Pow!h,2) + #NCl;
  vprintf HilbertModularForms: "dim(S_2) + #Cl^+(F) = %o\n", chi2;
  return chi1 eq chi2;
end intrinsic;

// TODO
intrinsic KodairaDimension(Gamma::GrpHilbert) -> MonStgElt
  {Returns the Kodaira dimension of the Hilbert modular surface associated to Gamma.
  Currently just returns -100}
    error "Not Implemented";
  return -100; // FIXME
end intrinsic;

// Could be improved in the future.
intrinsic KodairaDimensionPossibilities(Gamma::GrpHilbert) -> MonStgElt
{Returns a list of possible Kodaira dimensions of the Hilbert modular surface associated to
 Gamma, based on the arithmetic genus. When the level is 1, it
 gives a more refined list based on K^2. Currently only implemented for Gamma0.}

  require GammaType(Gamma) eq "Gamma0": "Only implemented for Gamma0";
  F := BaseField(Gamma);
  ZF := Integers(F);
  NCl, mp := NarrowClassGroup(F);
  chi := ArithmeticGenus(Gamma);

  if (Level(Gamma) eq 1*ZF) then //In level 1, we have the RationalityCriterion and we know the value of K2 of the minimal model exactly.
      // This is not true! We know the value of K2 exactly only if the surface is not rational!
    k2 := K2(Gamma) + getHZExceptionalNum(Gamma);
    if (k2 eq 0) then
        if (chi ge 3) then
            return [1];
        else
            return [0, 1];
        end if;
    else // k2 > 0
        if (chi eq 1) then
	    // Eran: We need to allow also for the case of the surface being rational
            if RationalityCriterion(Gamma) then
                return [-1];
            // elif (k2 eq 8) or (k2 eq 9) then
            //     return [-1, 2];
            else
                // return [2];
		return [-1,2];
            end if;
        else // chi not 1
            return [2];
        end if;
    end if;
  else // Not level 1, so we don't have RationalityCriterion yet and we don't know the number of exceptional curves, so K2(minimal model) >= K2(Gamma).
    k2 := K2(Gamma);
    if (k2 ge 1) then //The only options are [-1, 2]
        if (chi eq 1) then
            if (k2 ge 10) then
                return [2];
            else
                return [-1,2];
            end if;
        else
            return [2];
        end if;
    else // k2 is smaller then 0, so the lower bound is useless
        if (chi eq 1) then
            return [-1, 0, 1, 2];
        elif (chi ge 3) then
            return [1,2];
        else
            return [0,1,2];
        end if;
    end if;

  end if;
end intrinsic;

// Could be improved in the future.
intrinsic KodairaDimensionPossibilitiesWithHZ(Gamma::GrpHilbert) -> MonStgElt
{Returns a list of possible Kodaira dimensions of the Hilbert modular surface associated to
 Gamma, based on the arithmetic genus and the rationality criterion. When the level is 1, it
 gives a more refined list based on K^2. Currently only implemented for Gamma0.}

  require GammaType(Gamma) eq "Gamma0": "Only implemented for Gamma0";
  F := BaseField(Gamma);
  ZF := Integers(F);
  NCl, mp := NarrowClassGroup(F);
  chi := ArithmeticGenus(Gamma);

  if (chi eq 1) then
    if (Level(Gamma) eq 1*ZF) or ((Component(Gamma) @@ mp) eq NCl.0) then
      if RationalityCriterion(Gamma) then
        return [-1];
      else
        return [-1, 2];
      end if;
    else
      return [-1, 2];
    end if;
  else
    if Norm(Level(Gamma)) eq 1 then
      k2 := K2(Gamma) + getHZExceptionalNum(Gamma); //K2 of the minimal model of the HMS.
      if (chi eq 2) and (k2 eq 0) then
        return [0, 1];
      elif (chi ge 1) and (k2 eq 0) then
        return [1];
      else
        return [2];
      end if;
    else // We don't yet know the number of exceptional curves, so K2(minimal model) >= K2(Gamma).
      k2 := K2(Gamma);
      if (chi eq 2) and (k2 le 0) then
        return [0, 1, 2];
      elif (chi ge 1) and (k2 le 0) then
        return [1, 2];
      else
        return [2];
    end if;

    end if;

  end if;
end intrinsic;

intrinsic PrimeDiscriminant(D,q) -> MonStgElt
    {Given q|D, return +-q^(Valuation(D,q)) as needed in getHZExceptionalNum. }
    assert D mod q eq 0;
    assert IsFundamentalDiscriminant(D);
    sign := (q mod 4 eq 1) select 1 else -1;
    if (q eq 2) then
      sign_list := [(-1) : p in PrimeDivisors(D) | p mod 4 eq 3];
      if #sign_list eq 0 then
        sign := 1;
      else
       sign := &*sign_list;
      end if;
      end if;
    return sign*q^Valuation(D,q);
end intrinsic;

intrinsic getHZExceptionalNum(Gamma) -> MonStgElt
{Returns number of exceptional HZ divisors if the surface is *not rational*;
 currently only implemented for level 1.}

    require Norm(Level(Gamma)) eq 1 : "Only implemented for level 1";

    A := Norm(Component(Gamma));
    D := Discriminant(Integers(BaseField(Gamma)));
    qs := PrimeDivisors(D);
    Dqs := [PrimeDiscriminant(D,q) : q in qs];
    s := 2*&*[1 + KroneckerSymbol(Dq,A) : Dq in Dqs];
    s +:= &*[1 + KroneckerSymbol(Dq, 2*A) : Dq in Dqs];
    s +:= &*[1 + KroneckerSymbol(Dq, 3*A) : Dq in Dqs] div 2;
    s +:= (1 - KroneckerSymbol(D,3)^2)*
          &*[1 + KroneckerSymbol(Dq,9*A) : Dq in Dqs];
    if D eq 105 then
        s +:= 2;
    end if;
    return s;
end intrinsic;

intrinsic RationalityCriterion(Gamma) -> BoolElt
{Checks whether the Rationality Criterion is satisfied.
 Note: Only implemented for level 1.}

    require GammaType(Gamma) eq "Gamma0": "Only implemented for Gamma0";
    require IsOne(Level(Gamma)): "Only implemented for level 1";

    F := BaseField(Gamma);

    //Make a list of intersection numbers of cuspidal resolution cycles.
    res := CuspsWithResolution(Gamma);
    self_int_res := [];
    for x in res do
      for y in [1..x[4]] do
          self_int_res cat:= x[3];
      end for;
    end for;

    LevelList := [];

    //Make a list of possible exceptional Hirzebruch--Zagier divisors.
    if Norm(Level(Gamma)) eq 1 then //vdG VII.4 gives the following
      A := Component(Gamma);
      if Norm(A) eq 1 then
        Append(~LevelList, 1);
        Append(~LevelList, 4);
        Append(~LevelList, 9);
      end if;

      if NormEquation(F, 2*Norm(A)) then //2 is the norm of an ideal in the genus of A.
        Append(~LevelList, 2);
      end if;

      if NormEquation(F, 3*Norm(A)) then //3 is the norm of an ideal in the genus of A.
        Append(~LevelList, 3);
      end if;

    else //for now, only consider F_N if genus(F_N) = 0
        return false;
//      N := Generator(Level(Gamma) meet Integers());
//      require Norm(Component(Gamma)) eq 1: "Only principal genus supported for higher level.";
//      if N in [1 .. 10] cat [12, 13, 16, 18, 25] then
//        Append(~LevelList, N^2);
//      end if;
    end if;

    if #LevelList eq 0 then
      vprintf HilbertModularForms: "No exceptional HZ divisors found";
      return false;
    end if;

    //Compute intersections of HZ divisors with cusps.
    IntList := [];
    for M in LevelList do
      HZInt := HZCuspIntersection(Gamma, M);
      HZIntList := [];
      assert #HZInt eq #res;
      for i in [1 .. #HZInt] do
        for j in [1 .. res[i][4]] do
          HZIntList cat:= HZInt[i];
        end for;
      end for;
      Append(~IntList, HZIntList);
    end for;

    //Blow down any subset of the HZ divisors and check if we have a good configuration.
    for I in Subsets({1 .. #LevelList}) do
      if #I eq 0 then //Without blowing down, nothing to do.
        continue;
      else
        // List of indices s.t. boundary curve is now exceptional
        exc_indices := [i : i in [1 .. #self_int_res] |
                        self_int_res[i] + &+[ IntList[j][i] : j in I] eq -1];

        if #exc_indices le 1 then //One (-1)-curve is not enough!
          continue;
        end if;

        // For each two blown down expectional boundary curves, do they intersect?

        for S in Subsets(Set(exc_indices), 2) do
          T := SetToSequence(S);
          for j in I do
            if IntList[j][T[1]] ne 0 and IntList[j][T[2]] ne 0 then
              vprintf HilbertModularForms: "Blow down curves F_N for N in %o\n",
                                           LevelList[SetToSequence(I)];
              return true;
            end if;
          end for;
        end for;
      end if;

    end for;

    return false;
end intrinsic;



/*
// is this still right even when we haven't blown down?
intrinsic EasyIsGeneralType(hs::SeqEnum) -> Any
  {}
  chi, k2 := Explode(HodgeToChiK2(hs));
  if (chi gt 1) and (k2 gt 0) then
    return true;
  end if;
  return false;
end intrinsic;
*/

intrinsic HodgeToChiK2(hs::SeqEnum) -> Any
{Compute the Arithmetic Genus and c_1^2 from Hodge numbers h^(2,0) and h^(1,1).}
  h20, h11 := Explode(hs);
  chi := h20 + 1;
  c12 := 10*(h20 + 1) - h11;
  return [chi, c12];
end intrinsic;

intrinsic DimensionOfCuspForms(Gamma::GrpHilbert, k::RngIntElt) -> RngIntElt
{Use [vdG 4.4] to compute the dimension.}
  assert IsEven(k) and (k gt 0);
  if (k eq 2) then
      return ArithmeticGenus(Gamma) - 1;
  end if;

  vol := VolumeOfFundamentalDomain(Gamma);

  dim := ((k-1)^2 / 4) * vol;
  m := k div 2;

  // get elliptic points contribution
  a := CountEllipticPoints(Gamma);

  elliptic := 0;
  for rot_factor in Keys(a) do
    rot_tup := IntegerTuple(rot_factor);
    n := rot_tup[1];
    // normalize to type (q,1)
    assert rot_tup[2] eq 1;
    // q := rot_tup[2] * rot_tup[3]^(-1) mod n;
    q_inv := rot_tup[3];
    _, q, _ := XGCD(q_inv,n);
    Qn<zeta> := CyclotomicField(n);
    cont := &+[zeta^(i*(q+1)*m)/(n*(1-zeta^i)*(1-zeta^(i*q)))
	       : i in [1..n-1]];
    elliptic +:= cont*a[rot_factor];
  end for;

  dim +:= elliptic;

  // get cusp contribution
  cusps := CuspsWithResolution(Gamma);

  chi := 0;
  for cusp in cusps do
    _, _, L, n := Explode(cusp);
    if (n eq 1) and (#L eq 1) then
        chi +:= 1/12*(1+L[1]);
    else
	chi +:= n/12*&+[3+b : b in L];
    end if;
  end for;

  dim +:= chi;

  return dim;
end intrinsic;

intrinsic HilbertSeries(Gamma::GrpHilbert) -> FldFunRatUElt
{Compute the Hilbert series of a Hilbert modular surface. }
  // R<k> := PolynomialRing(Rationals());
  R<t> := FunctionField(Rationals());
  
  vol := VolumeOfFundamentalDomain(Gamma);

  hilb := vol*(2*t^2/(1-t)^3 + 1/(4*(1-t)) - 1/4*(1+t));
  
  // dim := ((2*k-1)^2 / 4) * vol;
  
  // get cusp contribution
  cusps := CuspsWithResolution(Gamma);

  chi := 0;
  for cusp in cusps do
    _, _, L, n := Explode(cusp);
    if (n eq 1) and (#L eq 1) then
        chi +:= 1/12*(1+L[1]);
    else
	chi +:= n/12*&+[3+b : b in L];
    end if;
  end for;

  hilb +:= chi*t^2/(1-t);
  // dim +:= chi;
  
  modulus := LCM({Tuple(k)[1] : k in Keys(EllipticPointData(Gamma))});
    
  // get elliptic points contribution
  a := CountEllipticPoints(Gamma);

  elliptic := [CyclotomicField(modulus) | 0 : m in [0..modulus-1]];
  for m in [0..modulus-1] do
      for rot_factor in Keys(a) do
	  rot_tup := IntegerTuple(rot_factor);
	  n := rot_tup[1];
	  // normalize to type (q,1)
	  assert rot_tup[2] eq 1;
	  // q := rot_tup[2] * rot_tup[3]^(-1) mod n;
	  q_inv := rot_tup[3];
	  _, q, _ := XGCD(q_inv,n);
	  Qn<zeta> := CyclotomicField(n);
	  cont := &+[zeta^(i*(q+1)*m)/(n*(1-zeta^i)*(1-zeta^(i*q)))
		     : i in [1..n-1]];
	  elliptic[m+1] +:= cont*a[rot_factor];
      end for;
  end for;
  
  elliptic := [Rationals()!e : e in elliptic];

  hilb +:= &+[elliptic[m+1]*t^m : m in [0..modulus-1]] / (1-t^modulus);
  hilb -:= elliptic[1] + elliptic[2]*t;
  
  // adding cups (Eisenstein series) contribution
  
  hilb +:= #cusps*t/(1-t);
  
  // finally adding the first two terms
  
  hilb +:= 1 + DimensionOfCuspForms(Gamma,2)*t;
  
  return hilb;    
end intrinsic;
    
