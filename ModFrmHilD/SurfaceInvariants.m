intrinsic EllipticPointResolution(order::RngIntElt, rot_factor::RngIntElt) ->
          SeqEnum[RngIntElt], SeqEnum[FldRatElt], SeqEnum[FldRatElt]
{}
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
{}
  c,x,y := EllipticPointResolution(order, rot_factor);
  a := [x[i]+y[i]-1 : i in [2..#c+1]];
  sq := -(&+[a[i]^2*c[i] : i in [1..#c]]);
  k2 := sq + 2*&+[Rationals() | a[i]*a[i+1] : i in [1..#c-1]];

  return k2, #c;
end intrinsic;

intrinsic EulerNumber(Gamma::GrpHilbert) -> RngIntElt
{}
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
{}
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

intrinsic ArithmeticGenus(Gamma::GrpHilbert) -> RngIntElt
{}
  chi := K2(Gamma) + EulerNumber(Gamma);
  assert chi mod 12 eq 0;
  return chi div 12;
end intrinsic;

intrinsic Irregularity(Gamma::GrpHilbert) -> RngIntElt
{}
  return 0;
end intrinsic;

intrinsic GeometricGenus(Gamma::GrpHilbert) -> RngIntElt
{}
  return ArithmeticGenus(Gamma)-1;
end intrinsic;

intrinsic HodgeDiamond(Gamma::GrpHilbert) -> RngIntEltt
{}
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

//To be improved
intrinsic KodairaDimensionPossibilities(Gamma::GrpHilbert) -> MonStgElt
{Returns a list of possible Kodaira dimensions of the Hilbert modular surface associated to 
Gamma, based on the arithmetic genus. When the level is 1, it gives a more refined list based 
on K^2.}

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
    {}
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
 Note 1: Only implemented for Gamma0(N) level.
 Note 2: it could be refined by including more Hirzebruch--Zagier divisors.}
    require GammaType(Gamma) eq "Gamma0": "Only implemented for Gamma0";

    F := BaseField(Gamma);

    //Make a list of intersection numbers of cusps.
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
      N := Generator(Level(Gamma) meet Integers());
      require Norm(Component(Gamma)) eq 1: "Only principal genus supported for higher level.";
      if N in [1 .. 10] cat [12, 13, 16, 18, 25] then
        Append(~LevelList, N^2);
      end if;
    end if;

    if #LevelList eq 0 then
      vprintf HilbertModularForms: "No exceptional HZ divisors found";
      return false;
    end if;

    // print LevelList;

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

    // print IntList;

    //Check if any (-1)-curves on the boundary give rationality.

    // for i in [1 .. #(self_int_res)] do
    //   if self_int_res[i] eq -1 then
    //     for j in [1 .. #(LevelList)] do
    //       if not IntList[j][i][1] eq 0 then
    //         vprintf HilbertModularForms:
    //                  "Exceptional curve on boundary intersects exceptional HZ divisor\n";
    //         return true;
    //       end if;
    //     end for;
    //   end if;
    // end for;

    //Blow down any subset of the HZ divisors and check if we have a good configuration.
    for I in Subsets({1 .. #LevelList}) do
      if #I eq 0 then //Without blowing down, nothing to do. 
        continue;
        // exc_indices := [i : i in [1 .. #self_int_res] | self_int_res[i] eq -1];
        //
        // for i in exc_indices do
        //   for j in [1 .. #LevelList] do
        //     if not IntList[j][i] eq 0 then
        //       vprintf HilbertModularForms:
        //              "Exceptional curve on boundary intersects exceptional HZ divisor\n";
        //       return true;
        //     end if;
        //   end for;
        // end for;
      else

        // List of indices s.t. boundary curve is now exceptional
        exc_indices := [i : i in [1 .. #self_int_res] |
                        self_int_res[i] + &+[ IntList[j][i] : j in I] eq -1];
        // Error in &+[ IntList[j][i] : j in I], seems like I'm still adding lists!

        if #exc_indices le 1 then //One (-1) curve is not enough!
          continue;
        end if;

        // For each two expectional boundary curves, do they intersect?

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

// IO
intrinsic WriteGeometricInvariantsToRow(Gamma::GrpHilbert) -> MonStgElt
{Script for writing geometric invariants to data table row. 
Format is label:[h^[2,0], h^[1,1]]:K^2:chi.}
  h2 := HodgeDiamond(Gamma)[3];
  return StripWhiteSpace(Join([
        LMFDBLabel(Gamma),
        //Sprint(KodairaDimension(Gamma)),
        Sprint(h2[1..2]),
        Sprint(K2(Gamma)),
        Sprint(ArithmeticGenus(Gamma))
  ], ":"));
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
{}
  h20, h11 := Explode(hs);
  chi := h20 + 1;
  c12 := 10*(h20 + 1) - h11;
  return [chi, c12];
end intrinsic;
