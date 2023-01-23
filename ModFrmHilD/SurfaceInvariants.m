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
  //for n in Keys(a) do
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
  //end for;

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

  // require D notin [8,12]: "Discriminant not supported";
  // require (Level(Gamma) eq 1*ZF) or (GCD(Level(Gamma), 3*D*ZF) eq 1*ZF):
  //		"Level is not supported";

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
  {Compute the arithmetic genus as (1/12)*(K^2 + e), summed over all components, and as dim(S_2) + #Cl^+(F); return true if these are equal. Currently only for GL+ type.}

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
  {Returns the Kodaira dimension of the Hilbert modular surface associated to Gamma. Currently just returns -100}
  return -100; // FIXME
end intrinsic;

//To be improved
intrinsic KodairaDimensionPossibilities(Gamma::GrpHilbert) -> MonStgElt
  {Returns a list of possible Kodaira dimensions of the Hilbert modular surface associated to Gamma,
    based on the arithmetic genus. When the level is 1, it gives a more refined list based on K^2.
  }

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
    //         vprintf HilbertModularForms: "Exceptional curve on boundary intersects exceptional HZ divisor\n";
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
        //       vprintf HilbertModularForms: "Exceptional curve on boundary intersects exceptional HZ divisor\n";
        //       return true;
        //     end if;
        //   end for;
        // end for;
      else

        // List of indices s.t. boundary curve is now exceptional
        exc_indices := [i : i in [1 .. #self_int_res] | self_int_res[i] + &+[ IntList[j][i] : j in I] eq -1];
        // Error in &+[ IntList[j][i] : j in I], seems like I'm still adding lists!

        if #exc_indices le 1 then //One (-1) curve is not enough!
          continue;
        end if;

        // For each two expectional boundary curves, do they intersect?

        for S in Subsets(Set(exc_indices), 2) do
          T := SetToSequence(S);
          for j in I do
            if IntList[j][T[1]] ne 0 and IntList[j][T[2]] ne 0 then
              vprintf HilbertModularForms: "Blow down curves F_N for N in %o\n", LevelList[SetToSequence(I)];
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
  {Script for writing geometric invariants to data table row. Format is label:[h^[2,0], h^[1,1]]:K^2:chi.}
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


intrinsic vanderGeerTable( : Discriminants := []) -> List
  {Return the table of invariants from pp. 269-276 of van der Geer. dot and unlisted values are returned as -100. If Discriminants is nonempty, return only those rows of the table with the corresponding discriminants.}
  dot := -100;
  unk := -100; // Unlisted value.
  table :=
  [*
    [* 5, -1, [1], 2, 1, 1, 1, 14, 1, dot, 1, 12, 0 *],
    [* 8, -1, [1], 2, 1, 1, 2, 15, 1, dot, 1, 13, 0 *],
    [* 12, 1, [1, 1], 3, 2, 0, 2, 16, 1, dot, 1, 14, 0 *],
    [* 12, 1, [-1, -1], 3, 0, 2, 4, 16, 1, dot, 1, 14, 0 *],
    [* 13, -1, [1], 2, 2, 2, 3, 15, 1, dot, 1, 13, 0 *],
    [* 17, -1, [1], 4, 1, 1, 5, 16, 1, dot, 1, 14, 0 *],
    [* 21, 1, [1, 1], 4, 4, 1, 2, 18, 1, dot, unk, unk, unk *],
    [* 21, 1, [-1, -1], 4, 1, 4, 6, 25, 2, 0, unk, unk, unk *],
    [* 24, 1, [1, 1], 6, 3, 0, 4, 19, 1, dot, unk, unk, unk *],
    [* 24, 1, [-1, -1], 6, 0, 3, 8, 26, 2, 0, unk, unk, unk *],
    [* 28, 1, [1, 1], 4, 2, 2, 4, 20, 1, dot, unk, unk, unk *],
    [* 28, 1, [-1, -1], 4, 2, 2, 10, 26, 2, 0, unk, unk, unk *],
    [* 29, -1, [1], 6, 3, 3, 5, 28, 2, 0, 2, 23, 1 *],
    [* 33, 1, [1, 1], 4, 3, 0, 8, 21, 1, dot, unk, unk, unk *],
    [* 33, 1, [-1, -1], 4, 0, 3, 12, 28, 2, 0, unk, unk, unk *],
    [* 37, -1, [1], 2, 4, 4, 7, 29, 2, 0, 2, 24, 1 *],
    [* 40, -1, [1, 1], 6, 2, 2, 12, 32, 2, 0, unk, unk, unk *],
    [* 40, -1, [-1, -1], 6, 2, 2, 8, 28, 2, 0, unk, unk, unk *],
    [* 41, -1, [1], 8, 1, 1, 11, 30, 2, 0, 2, 25, 1 *],
    [* 44, 1, [1, 1], 10, 2, 2, 6, 32, 2, 0, unk, unk, unk *],
    [* 44, 1, [-1, -1], 10, 2, 2, 12, 38, 3, 0, unk, unk, unk *],
    [* 53, -1, [1], 6, 5, 5, 7, 40, 3, 0, 3, 32, 2 *],
    [* 56, 1, [1, 1], 12, 2, 2, 4, 34, 2, 0, unk, unk, unk *],
    [* 56, 1, [-1, -1], 12, 2, 2, 16, 46, 4, 2, unk, unk, unk *],
    [* 57, 1, [1, 1], 4, 4, 1, 14, 34, 2, 0, unk, unk, unk *],
    [* 57, 1, [-1, -1], 4, 1, 4, 18, 41, 3, 0, unk, unk, unk *],
    [* 60, 1, [1, 1, 1], 8, 6, 0, 4, 30, 1, unk, unk, unk, unk *],
    [* 60, 1, [-1, -1, 1], 8, 0, 6, 24, 56, 5, 4, unk, unk, unk *],
    [* 60, 1, [-1, 1, -1], 8, 6, 0, 12, 38, 3, 0, unk, unk, unk *],
    [* 60, 1, [1, -1, -1], 8, 0, 6, 8, 40, 3, 0, unk, unk, unk *],
    [* 61, -1, [1], 6, 4, 4, 11, 41, 3, 0, 3, 33, 2 *],
    [* 65, -1, [1, 1], 8, 2, 2, 18, 44, 3, 0, unk, unk, unk *],
    [* 65, -1, [-1, -1], 8, 2, 2, 14, 40, 3, 0, unk, unk, unk *],
    [* 69, 1, [1, 1], 8, 9, 0, 4, 35, 2, 2, unk, unk, unk *],
    [* 69, 1, [-1, -1], 8, 0, 9, 16, 56, 5, 4, unk, unk, unk *],
    [* 73, -1, [1], 4, 2, 2, 21, 43, 3, 0, 3, 35, 2 *],
    [* 76, 1, [1, 1], 10, 2, 2, 14, 44, 3, 0, unk, unk, unk *],
    [* 76, 1, [-1, -1], 10, 2, 2, 20, 50, 4, 2, unk, unk, unk *],
    [* 77, 1, [1, 1], 8, 6, 6, 2, 44, 3, 0, unk, unk, unk *],
    [* 77, 1, [-1, -1], 8, 6, 6, 14, 56, 5, 4, unk, unk, unk *],
    [* 85, -1, [1, 1], 4, 6, 6, 18, 56, 4, 0, unk, unk, unk *],
    [* 85, -1, [1, 1], 4, 6, 6, 10, 48, 4, 2, unk, unk, unk *],
    [* 88, 1, [1, 1], 6, 4, 4, 12, 46, 3, 0, unk, unk, unk *],
    [* 88, 1, [-1, -1], 6, 4, 4, 24, 58, 5, 4, unk, unk, unk *],
    [* 89, -1, [1], 12, 1, 1, 21, 52, 4, 2, 4, 41, 3 *],
    [* 92, 1, [1, 1], 12, 4, 4, 4, 46, 3, 0, unk, unk, unk *],
    [* 92, 1, [-1, -1], 12, 4, 4, 22, 64, 6, 8, unk, unk, unk *],
    [* 93, 1, [1, 1], 4, 12, 3, 6, 46, 3, 0, unk, unk, unk *],
    [* 93, 1, [-1, -1], 4, 3, 12, 18, 67, 6, 6, unk, unk, unk *],
    [* 97, -1, [1], 4, 2, 2, 27, 53, 4, 2, 4, 42, 3 *],
    [* 101, -1, [1], 14, 5, 5, 11, 60, 5, 4, 5, 46, 4 *],
    [* 104, -1, [1, 1], 18, 2, 2, 20, 64, 5, 4, unk, unk, unk *],
    [* 104, -1, [-1, -1], 18, 2, 2, 12, 56, 5, 6, unk, unk, unk *],
    [* 105, 1, [1, 1, 1], 8, 6, 0, 12, 46, 2, 0, unk, unk, unk *],
    [* 105, 1, [-1, -1, 1], 8, 0, 6, 16, 56, 4, 0, unk, unk, unk *],
    [* 105, 1, [-1, 1, -1], 8, 0, 6, 44, 84, 8, 12, unk, unk, unk *],
    [* 105, 1, [1, -1, -1], 8, 6, 0, 32, 66, 6, 8, unk, unk, unk *],
    [* 109, -1, [1], 6, 6, 6, 17, 61, 5, 4, 5, 47, 4 *],
    [* 113, -1, [1], 8, 3, 3, 23, 60, 5, 6, 5, 46, 4 *],
    [* 120, 1, [1, 1, 1], 12, 8, 2, 8, 56, 3, 0, unk, unk, unk *],
    [* 120, 1, [-1, -1, 1], 12, 2, 8, 40, 94, 9, 14, unk, unk, unk *],
    [* 120, 1, [-1, 1, -1], 12, 8, 2, 24, 72, 7, 12, unk, unk, unk *],
    [* 120, 1, [1, -1, -1], 12, 2, 8, 8, 62, 5, 4, unk, unk, unk *],
    [* 124, 1, [1, 1], 12, 2, 2, 16, 56, 4, 2, unk, unk, unk *],
    [* 124, 1, [-1, -1], 12, 2, 2, 34, 74, 7, 12, unk, unk, unk *],
    [* 129, 1, [1, 1], 12, 4, 1, 30, 74, 6, 8, unk, unk, unk *],
    [* 129, 1, [-1, -1], 12, 1, 4, 34, 81, 7, 8, unk, unk, unk *],
    [* 133, 1, [1, 1], 4, 8, 8, 12, 64, 5, 4, unk, unk, unk *],
    [* 133, 1, [-1, -1], 4, 8, 8, 24, 76, 7, 10, unk, unk, unk *],
    [* 136, 1, [1, 1], 12, 2, 2, 32, 74, 6, 8, unk, unk, unk *],
    [* 136, 1, [-1, -1], 12, 2, 2, 20, 62, 6, 12, unk, unk, unk *],
    [* 137, -1, [1], 8, 3, 3, 27, 68, 6, 10, 6, 51, 5 *],
    [* 140, 1, [1, 1, 1], 20, 4, 4, 4, 64, 4, 0, unk, unk, unk *],
    [* 140, 1, [-1, -1, 1], 20, 4, 4, 8, 68, 6, 8, unk, unk, unk *],
    [* 140, 1, [-1, 1, -1], 20, 4, 4, 40, 100, 10, 20, unk, unk, unk *],
    [* 140, 1, [1, -1, -1], 20, 4, 4, 20, 80, 8, 16, unk, unk, unk *],
    [* 141, 1, [1, 1], 8, 15, 0, 8, 57, 4, 2, unk, unk, unk *],
    [* 141, 1, [-1, -1], 8, 0, 15, 28, 92, 9, 16, unk, unk, unk *],
    [* 145, -1, [1, 1], 8, 2, 2, 40, 82, 7, 10, unk, unk, unk *],
    [* 145, -1, [-1, -1], 8, 2, 2, 36, 78, 7, 12, unk, unk, unk *],
    [* 149, -1, [1], 14, 7, 7, 15, 78, 7, 10, 7, 58, 6 *],
    [* 156, 1, [1, 1, 1], 16, 8, 2, 16, 76, 5, 4, unk, unk, unk *],
    [* 156, 1, [-1, -1, 1], 16, 2, 8, 48, 114, 11, 20, unk, unk, unk *],
    [* 156, 1, [-1, 1, -1], 16, 8, 2, 28, 88, 9, 20, unk, unk, unk *],
    [* 156, 1, [1, -1, -1], 16, 2, 8, 12, 78, 7, 10, unk, unk, unk *],
    [* 157, -1, [1], 6, 8, 8, 19, 77, 7, 12, 7, 57, 6 *],
    [* 161, 1, [1, 1], 16, 2, 2, 14, 68, 5, 4, unk, unk, unk *],
    [* 161, 1, [-1, -1], 16, 2, 2, 50, 104, 11, 28, unk, unk, unk *],
    [* 165, 1, [1, 1, 1], 8, 16, 4, 4, 68, 4, 0, unk, unk, unk *],
    [* 165, 1, [-1, -1, 1], 8, 4, 16, 8, 84, 8, 14, unk, unk, unk *],
    [* 165, 1, [-1, 1, -1], 8, 4, 16, 44, 120, 12, 24, unk, unk, unk *],
    [* 165, 1, [1, -1, -1], 8, 16, 4, 16, 80, 8, 16, unk, unk, unk *],
    [* 168, 1, [1, 1, 1], 12, 12, 0, 8, 64, 4, 4, unk, unk, unk *],
    [* 168, 1, [-1, -1, 1], 12, 0, 12, 16, 84, 8, 16, unk, unk, unk *],
    [* 168, 1, [-1, 1, -1], 12, 12, 0, 24, 80, 8, 18, unk, unk, unk *],
    [* 168, 1, [1, -1, -1], 12, 0, 12, 48, 116, 12, 28, unk, unk, unk *],
    [* 172, 1, [1, 1], 10, 6, 6, 26, 88, 8, 16, unk, unk, unk *],
    [* 172, 1, [-1, -1], 10, 6, 6, 32, 94, 9, 18, unk, unk, unk *],
    [* 173, -1, [1], 14, 9, 9, 13, 86, 8, 14, 8, 63, 7 *],
    [* 177, 1, [1, 1], 4, 9, 0, 32, 79, 7, 16, unk, unk, unk *],
    [* 177, 1, [-1, -1], 4, 0, 9, 44, 100, 10, 24, unk, unk, unk *],
    [* 181, -1, [1], 10, 6, 6, 25, 85, 8, 16, 8, 62, 7 *],
    [* 184, 1, [1, 1], 12, 4, 4, 16, 76, 6, 8, unk, unk, unk *],
    [* 184, 1, [-1, -1], 12, 4, 4, 52, 112, 12, 32, unk, unk, unk *],
    [* 185, -1, [1, 1], 16, 2, 2, 38, 96, 9, 20, unk, unk, unk *],
    [* 185, -1, [-1, -1], 16, 2, 2, 30, 88, 9, 24, unk, unk, unk *],
    [* 188, 1, [1, 1], 20, 4, 4, 4, 70, 6, 12, unk, unk, unk *],
    [* 188, 1, [-1, -1], 20, 4, 4, 34, 100, 11, 32, unk, unk, unk *],
    [* 193, -1, [1], 4, 4, 4, 47, 103, 10, 24, 8, 72, 11 *],
    [* 197, -1, [1], 10, 11, 11, 15, 94, 9, 18, 9, 68, 8 *],
    [* 201, 1, [1, 1], 12, 4, 1, 42, 102, 10, 28, unk, unk, unk *],
    [* 201, 1, [-1, -1], 12, 1, 4, 46, 109, 11, 28, unk, unk, unk *],
    [* 204, 1, [1, 1, 1], 20, 12, 0, 28, 104, 8, 12, unk, unk, unk *],
    [* 204, 1, [-1, -1, 1], 20, 0, 12, 56, 144, 14, 28, unk, unk, unk *],
    [* 204, 1, [-1, 1, -1], 20, 12, 0, 20, 96, 10, 26, unk, unk, unk *],
    [* 204, 1, [1, -1, -1], 20, 0, 12, 24, 112, 12, 32, unk, unk, unk *],
    [* 205, 1, [1, 1], 8, 10, 10, 32, 110, 10, 18, unk, unk, unk *],
    [* 205, 1, [-1, -1], 8, 10, 10, 20, 98, 10, 24, unk, unk, unk *],
    [* 209, 1, [1, 1], 20, 2, 2, 32, 102, 10, 26, unk, unk, unk *],
    [* 209, 1, [-1, -1], 20, 2, 2, 44, 114, 12, 34, unk, unk, unk *],
    [* 213, 1, [1, 1], 8, 21, 0, 4, 71, 6, 12, unk, unk, unk *],
    [* 213, 1, [-1, -1], 8, 0, 21, 32, 120, 13, 36, unk, unk, unk *],
    [* 217, 1, [1, 1], 8, 4, 4, 32, 100, 9, 20, unk, unk, unk *],
    [* 217, 1, [-1, -1], 8, 4, 4, 68, 136, 15, 46, unk, unk, unk *],
    [* 220, 1, [1, 1, 1], 16, 4, 4, 16, 88, 7, 12, unk, unk, unk *],
    [* 220, 1, [-1, -1, 1], 16, 4, 4, 32, 104, 11, 32, unk, unk, unk *],
    [* 220, 1, [-1, 1, -1], 16, 4, 4, 64, 136, 15, 44, unk, unk, unk *],
    [* 220, 1, [1, -1, -1], 16, 4, 4, 32, 104, 11, 32, unk, unk, unk *],
    [* 221, 1, [1, 1], 16, 8, 8, 28, 108, 10, 20, unk, unk, unk *],
    [* 221, 1, [-1, -1], 16, 8, 8, 12, 92, 10, 28, unk, unk, unk *],
    [* 229, -1, [1], 10, 6, 6, 29, 97, 10, 28, 10, 68, 9 *],
    [* 232, -1, [1, 1], 6, 6, 6, 40, 108, 11, 32, unk, unk, unk *],
    [* 232, -1, [-1, -1], 6, 6, 6, 32, 100, 11, 36, unk, unk, unk *],
    [* 233, -1, [1], 12, 5, 5, 39, 114, 12, 36, 10, 77, 13 *],
    [* 236, 1, [1, 1], 30, 2, 2, 18, 100, 10, 28, unk, unk, unk *],
    [* 236, 1, [-1, -1], 30, 2, 2, 36, 118, 13, 40, unk, unk, unk *],
    [* 237, 1, [1, 1], 12, 20, 5, 10, 98, 9, 20, unk, unk, unk *],
    [* 237, 1, [-1, -1], 12, 5, 20, 30, 133, 14, 36, unk, unk, unk *],
    [* 241, -1, [1], 12, 2, 2, 59, 133, 14, 42, 10, 88, 17 *],
    [* 248, 1, [1, 1], 24, 6, 6, 4, 94, 9, 24, unk, unk, unk *],
    [* 248, 1, [-1, -1], 24, 6, 6, 40, 130, 15, 50, unk, unk, unk *],
    [* 249, 1, [1, 1], 12, 9, 0, 48, 127, 13, 40, unk, unk, unk *],
    [* 249, 1, [-1, -1], 12, 0, 9, 60, 148, 16, 48, unk, unk, unk *],
    [* 253, 1, [1, 1], 4, 12, 12, 10, 98, 9, 20, unk, unk, unk *],
    [* 253, 1, [-1, -1], 4, 12, 12, 46, 134, 15, 46, unk, unk, unk *],
    [* 257, -1, [1], 16, 3, 3, 39, 116, 13, 46, 11, 76, 14 *],
    [* 264, 1, [1, 1, 1], 24, 8, 2, 32, 124, 11, 28, unk, unk, unk *],
    [* 264, 1, [-1, -1, 1], 24, 2, 8, 16, 114, 13, 44, unk, unk, unk *],
    [* 264, 1, [-1, 1, -1], 24, 8, 2, 32, 124, 15, 56, unk, unk, unk *],
    [* 264, 1, [1, -1, -1], 24, 2, 8, 64, 162, 17, 46, unk, unk, unk *],
    [* 265, -1, [1, 1], 8, 2, 2, 62, 136, 15, 52, unk, unk, unk *],
    [* 265, -1, [-1, -1], 8, 2, 2, 58, 132, 15, 54, unk, unk, unk *],
    [* 268, 1, [1, 1], 10, 6, 6, 38, 120, 13, 44, unk, unk, unk *],
    [* 268, 1, [-1, -1], 10, 6, 6, 44, 126, 14, 46, unk, unk, unk *],
    [* 269, -1, [1], 22, 7, 7, 21, 112, 12, 36, 12, 77, 11 *],
    [* 273, 1, [1, 1, 1], 8, 8, 2, 28, 108, 10, 32, unk, unk, unk *],
    [* 273, 1, [-1, -1, 1], 8, 2, 8, 84, 170, 20, 72, unk, unk, unk *],
    [* 273, 1, [-1, 1, -1], 8, 2, 8, 24, 110, 12, 42, unk, unk, unk *],
    [* 273, 1, [1, -1, -1], 8, 8, 2, 64, 144, 18, 72, unk, unk, unk *],
    [* 277, -1, [1], 6, 14, 14, 29, 133, 14, 40, 12, 90, 15 *],
    [* 280, 1, [1, 1, 1], 12, 4, 4, 24, 104, 10, 32, unk, unk, unk *],
    [* 280, 1, [-1, -1, 1], 12, 4, 4, 40, 120, 14, 52, unk, unk, unk *],
    [* 280, 1, [-1, 1, -1], 12, 4, 4, 72, 152, 18, 64, unk, unk, unk *],
    [* 280, 1, [1, -1, -1], 12, 4, 4, 40, 120, 14, 52, unk, unk, unk *],
    [* 281, -1, [1], 20, 3, 3, 49, 142, 16, 56, 12, 91, 19 *],
    [* 284, 1, [1, 1], 28, 4, 4, 12, 110, 11, 32, unk, unk, unk *],
    [* 284, 1, [-1, -1], 28, 4, 4, 54, 152, 18, 64, unk, unk, unk *],
    [* 285, 1, [1, 1, 1], 16, 24, 0, 4, 100, 8, 16, unk, unk, unk *],
    [* 285, 1, [-1, -1, 1], 16, 0, 24, 20, 140, 16, 52, unk, unk, unk *],
    [* 285, 1, [-1, 1, -1], 16, 0, 24, 60, 180, 20, 60, unk, unk, unk *],
    [* 285, 1, [1, -1, -1], 16, 24, 0, 12, 108, 12, 38, unk, unk, unk *],
    [* 293, -1, [1], 18, 11, 11, 17, 120, 13, 40, 13, 82, 12 *],
    [* 296, -1, [1, 1], 30, 6, 6, 40, 152, 16, 48, unk, unk, unk *],
    [* 296, -1, [-1, -1], 30, 6, 6, 28, 140, 16, 54, unk, unk, unk *],
    [* 301, 1, [1, 1], 8, 8, 8, 30, 118, 13, 46, unk, unk, unk *],
    [* 301, 1, [-1, -1], 8, 8, 8, 42, 130, 15, 52, unk, unk, unk *],
    [* 305, 1, [1, 1], 16, 4, 4, 56, 152, 17, 60, unk, unk, unk *],
    [* 305, 1, [-1, -1], 16, 4, 4, 44, 140, 17, 68, unk, unk, unk *],
    [* 309, 1, [1, 1], 12, 20, 5, 22, 126, 13, 40, unk, unk, unk *],
    [* 309, 1, [-1, -1], 12, 5, 20, 42, 161, 18, 56, unk, unk, unk *],
    [* 312, 1, [1, 1, 1], 12, 18, 0, 8, 102, 9, 28, unk, unk, unk *],
    [* 312, 1, [-1, -1, 1], 12, 0, 18, 80, 192, 23, 84, unk, unk, unk *],
    [* 312, 1, [-1, 1, -1], 12, 18, 0, 40, 134, 17, 70, unk, unk, unk *],
    [* 312, 1, [1, -1, -1], 12, 0, 18, 16, 128, 15, 56, unk, unk, unk *],
    [* 313, -1, [1], 8, 4, 4, 65, 161, 19, 74, 13, 99, 24 *],
    [* 316, 1, [1, 1], 20, 6, 6, 36, 148, 16, 54, unk, unk, unk *],
    [* 316, 1, [-1, -1], 20, 6, 6, 66, 178, 21, 76, unk, unk, unk *],
    [* 317, -1, [1], 10, 13, 13, 21, 126, 14, 46, 14, 85, 13 *],
    [* 321, 1, [1, 1], 20, 9, 0, 56, 167, 19, 72, unk, unk, unk *],
    [* 321, 1, [-1, -1], 20, 0, 9, 68, 188, 22, 80, unk, unk, unk *],
    [* 328, -1, [1, 1], 12, 6, 6, 56, 154, 17, 60, unk, unk, unk *],
    [* 328, -1, [-1, -1], 12, 6, 6, 32, 130, 17, 76, unk, unk, unk *],
    [* 329, 1, [1, 1], 24, 4, 4, 24, 140, 15, 52, unk, unk, unk *],
    [* 329, 1, [-1, -1], 24, 4, 4, 84, 200, 25, 100, unk, unk, unk *],
    [* 332, 1, [1, 1], 30, 6, 6, 18, 132, 15, 56, unk, unk, unk *],
    [* 332, 1, [-1, -1], 30, 6, 6, 36, 150, 18, 68, unk, unk, unk *],
    [* 337, -1, [1], 8, 6, 6, 71, 185, 22, 86, 14, 112, 29 *],
    [* 341, 1, [1, 1], 28, 8, 8, 6, 122, 13, 42, unk, unk, unk *],
    [* 341, 1, [-1, -1], 28, 8, 8, 42, 158, 19, 70, unk, unk, unk *],
    [* 344, 1, [1, 1], 30, 4, 4, 32, 146, 17, 66, unk, unk, unk *],
    [* 344, 1, [-1, -1], 30, 4, 4, 44, 158, 19, 72, unk, unk, unk *],
    [* 345, 1, [1, 1, 1], 8, 8, 2, 28, 132, 14, 56, unk, unk, unk *],
    [* 345, 1, [-1, -1, 1], 8, 2, 8, 28, 138, 16, 64, unk, unk, unk *],
    [* 345, 1, [-1, 1, -1], 8, 2, 8, 108, 218, 28, 118, unk, unk, unk *],
    [* 345, 1, [1, -1, -1], 8, 8, 2, 92, 196, 26, 116, unk, unk, unk *],
    [* 348, 1, [1, 1, 1], 24, 18, 0, 12, 130, 13, 46, unk, unk, unk *],
    [* 348, 1, [-1, -1, 1], 24, 0, 18, 72, 208, 25, 92, unk, unk, unk *],
    [* 348, 1, [-1, 1, -1], 24, 18, 0, 36, 154, 19, 76, unk, unk, unk *],
    [* 348, 1, [1, -1, -1], 24, 0, 18, 24, 160, 19, 72, unk, unk, unk *],
    [* 349, -1, [1], 14, 8, 8, 37, 143, 17, 66, 15, 91, 18 *],
    [* 353, -1, [1], 16, 3, 3, 47, 148, 19, 86, 15, 88, 22 *],
    [* 357, 1, [1, 1, 1], 8, 30, 0, 4, 110, 10, 30, unk, unk, unk *],
    [* 357, 1, [-1, -1, 1], 8, 0, 30, 68, 204, 24, 84, unk, unk, unk *],
    [* 357, 1, [-1, 1, -1], 8, 0, 30, 24, 160, 20, 80, unk, unk, unk *],
    [* 357, 1, [1, -1, -1], 8, 30, 0, 8, 114, 14, 56, unk, unk, unk *],
    [* 364, 1, [1, 1, 1], 20, 4, 4, 48, 164, 18, 68, unk, unk, unk *],
    [* 364, 1, [-1, -1, 1], 20, 4, 4, 84, 200, 24, 92, unk, unk, unk *],
    [* 364, 1, [-1, 1, -1], 20, 4, 4, 40, 156, 20, 88, unk, unk, unk *],
    [* 364, 1, [1, -1, -1], 20, 4, 4, 52, 168, 22, 96, unk, unk, unk *],
    [* 365, -1, [1, 1], 20, 14, 14, 38, 172, 18, 52, unk, unk, unk *],
    [* 365, -1, [-1, -1], 20, 14, 14, 14, 148, 18, 68, unk, unk, unk *],
    [* 373, -1, [1], 10, 16, 16, 37, 175, 20, 70, 16, 112, 23 *],
    [* 376, 1, [1, 1], 24, 4, 4, 24, 148, 17, 68, unk, unk, unk *],
    [* 376, 1, [-1, -1], 24, 4, 4, 84, 208, 27, 116, unk, unk, unk *],
    [* 377, 1, [1, 1], 16, 4, 4, 56, 168, 21, 92, unk, unk, unk *],
    [* 377, 1, [-1, -1], 16, 4, 4, 44, 156, 21, 100, unk, unk, unk *],
    [* 380, 1, [1, 1, 1], 32, 8, 8, 8, 148, 15, 48, unk, unk, unk *],
    [* 380, 1, [-1, -1, 1], 32, 8, 8, 40, 180, 23, 96, unk, unk, unk *],
    [* 380, 1, [-1, 1, -1], 32, 8, 8, 80, 220, 27, 104, unk, unk, unk *],
    [* 380, 1, [1, -1, -1], 32, 8, 8, 16, 156, 19, 76, unk, unk, unk *],
    [* 381, 1, [1, 1], 20, 20, 5, 22, 150, 17, 64, unk, unk, unk *],
    [* 381, 1, [-1, -1], 20, 5, 20, 42, 185, 22, 80, unk, unk, unk *],
    [* 385, 1, [1, 1, 1], 8, 4, 4, 48, 172, 20, 84, unk, unk, unk *],
    [* 385, 1, [-1, -1, 1], 8, 4, 4, 92, 216, 28, 124, unk, unk, unk *],
    [* 385, 1, [-1, 1, -1], 8, 4, 4, 68, 192, 24, 104, unk, unk, unk *],
    [* 385, 1, [1, -1, -1], 8, 4, 4, 120, 244, 32, 140, unk, unk, unk *],
    [* 389, -1, [1], 22, 11, 11, 31, 162, 19, 70, 17, 104, 20 *],
    [* 393, 1, [1, 1], 12, 15, 0, 56, 185, 23, 102, unk, unk, unk *],
    [* 393, 1, [-1, -1], 12, 0, 15, 76, 220, 28, 120, unk, unk, unk *],
    [* 397, -1, [1], 6, 12, 12, 35, 153, 19, 80, 17, 95, 20 *],
    [* 401, -1, [1], 20, 3, 3, 65, 194, 25, 112, 17, 112, 32 *],
    [* 408, 1, [1, 1, 1], 12, 16, 4, 40, 164, 18, 72, unk, unk, unk *],
    [* 408, 1, [-1, -1, 1], 12, 4, 16, 80, 216, 26, 100, unk, unk, unk *],
    [* 408, 1, [-1, 1, -1], 12, 16, 4, 32, 156, 22, 108, unk, unk, unk *],
    [* 408, 1, [1, -1, -1], 12, 4, 16, 24, 160, 22, 106, unk, unk, unk *],
    [* 409, -1, [1], 16, 2, 2, 87, 225, 29, 130, 17, 127, 40 *],
    [* 412, 1, [1, 1], 20, 6, 6, 36, 168, 21, 94, unk, unk, unk *],
    [* 412, 1, [-1, -1], 20, 6, 6, 66, 198, 26, 116, unk, unk, unk *],
    [* 413, 1, [1, 1], 20, 16, 16, 4, 152, 17, 60, unk, unk, unk *],
    [* 413, 1, [-1, -1], 20, 16, 16, 40, 188, 23, 88, unk, unk, unk *],
    [* 417, 1, [1, 1], 12, 12, 3, 62, 202, 26, 120, unk, unk, unk *],
    [* 417, 1, [-1, -1], 12, 3, 12, 74, 223, 29, 130, unk, unk, unk *],
    [* 421, -1, [1], 10, 10, 10, 47, 175, 22, 94, 18, 106, 25 *],
    [* 424, -1, [1, 1], 18, 6, 6, 68, 208, 26, 112, unk, unk, unk *],
    [* 424, -1, [-1, -1], 18, 6, 6, 60, 200, 26, 116, unk, unk, unk *],
    [* 428, 1, [1, 1], 30, 10, 10, 26, 180, 22, 92, unk, unk, unk *],
    [* 428, 1, [-1, -1], 30, 10, 10, 44, 198, 25, 104, unk, unk, unk *],
    [* 429, 1, [1, 1, 1], 16, 30, 0, 8, 146, 14, 44, unk, unk, unk *],
    [* 429, 1, [-1, -1, 1], 16, 0, 30, 96, 264, 32, 120, unk, unk, unk *],
    [* 429, 1, [-1, 1, -1], 16, 0, 30, 20, 188, 24, 100, unk, unk, unk *],
    [* 429, 1, [1, -1, -1], 16, 30, 0, 28, 166, 22, 98, unk, unk, unk *],
    [* 433, -1, [1], 12, 4, 4, 81, 225, 30, 142, 18, 124, 41 *],
    [* 437, 1, [1, 1], 20, 14, 14, 2, 144, 17, 68, unk, unk, unk *],
    [* 437, 1, [-1, -1], 20, 14, 14, 38, 180, 23, 96, unk, unk, unk *],
    [* 440, 1, [1, 1, 1], 36, 4, 4, 8, 148, 17, 72, unk, unk, unk *],
    [* 440, 1, [-1, -1, 1], 36, 4, 4, 40, 180, 25, 120, unk, unk, unk *],
    [* 440, 1, [-1, 1, -1], 36, 4, 4, 80, 220, 29, 128, unk, unk, unk *],
    [* 440, 1, [1, -1, -1], 36, 4, 4, 16, 156, 21, 100, unk, unk, unk *],
    [* 444, 1, [1, 1, 1], 32, 8, 2, 32, 180, 21, 92, unk, unk, unk *],
    [* 444, 1, [-1, -1, 1], 32, 2, 8, 88, 242, 31, 132, unk, unk, unk *],
    [* 444, 1, [-1, 1, -1], 32, 8, 2, 60, 208, 29, 140, unk, unk, unk *],
    [* 444, 1, [1, -1, -1], 32, 2, 8, 20, 174, 23, 106, unk, unk, unk *],
    [* 445, -1, [1, 1], 8, 14, 14, 56, 202, 24, 94, unk, unk, unk *],
    [* 445, -1, [-1, -1], 8, 14, 14, 36, 182, 24, 108, unk, unk, unk *],
    [* 449, -1, [1], 20, 3, 3, 71, 216, 29, 138, 19, 120, 38 *],
    [* 453, 1, [1, 1], 12, 28, 7, 14, 158, 19, 80, unk, unk, unk *],
    [* 453, 1, [-1, -1], 12, 7, 28, 42, 207, 26, 106, unk, unk, unk *],
    [* 456, 1, [1, 1, 1], 24, 18, 0, 48, 202, 23, 94, unk, unk, unk *],
    [* 456, 1, [-1, -1, 1], 24, 0, 18, 40, 212, 29, 136, unk, unk, unk *],
    [* 456, 1, [-1, 1, -1], 24, 18, 0, 40, 194, 27, 132, unk, unk, unk *],
    [* 456, 1, [1, -1, -1], 24, 0, 18, 96, 268, 33, 132, unk, unk, unk *],
    [* 457, -1, [1], 8, 6, 6, 89, 247, 33, 156, 19, 135, 46 *],
    [* 460, 1, [1, 1, 1], 20, 4, 4, 20, 160, 20, 96, unk, unk, unk *],
    [* 460, 1, [-1, -1, 1], 20, 4, 4, 24, 164, 22, 108, unk, unk, unk *],
    [* 460, 1, [-1, 1, -1], 20, 4, 4, 104, 244, 34, 164, unk, unk, unk *],
    [* 460, 1, [1, -1, -1], 20, 4, 4, 84, 224, 32, 160, unk, unk, unk *],
    [* 461, -1, [1], 30, 9, 9, 29, 174, 22, 94, 20, 107, 23 *],
    [* 465, 1, [1, 1, 1], 16, 12, 0, 36, 192, 24, 116, unk, unk, unk *],
    [* 465, 1, [-1, -1, 1], 16, 0, 12, 44, 212, 28, 132, unk, unk, unk *],
    [* 465, 1, [-1, 1, -1], 16, 0, 12, 124, 292, 40, 188, unk, unk, unk *],
    [* 465, 1, [1, -1, -1], 16, 12, 0, 100, 256, 36, 178, unk, unk, unk *],
    [* 469, 1, [1, 1], 16, 12, 12, 42, 198, 25, 110, unk, unk, unk *],
    [* 469, 1, [-1, -1], 16, 12, 12, 54, 210, 27, 116, unk, unk, unk *],
    [* 472, 1, [1, 1], 18, 8, 8, 36, 190, 25, 120, unk, unk, unk *],
    [* 472, 1, [-1, -1], 18, 8, 8, 72, 226, 31, 148, unk, unk, unk *],
    [* 473, 1, [1, 1], 12, 6, 6, 56, 202, 28, 142, unk, unk, unk *],
    [* 473, 1, [-1, -1], 12, 6, 6, 68, 214, 30, 150, unk, unk, unk *],
    [* 476, 1, [1, 1, 1], 40, 4, 4, 8, 168, 18, 68, unk, unk, unk *],
    [* 476, 1, [-1, -1, 1], 40, 4, 4, 116, 276, 36, 156, unk, unk, unk *],
    [* 476, 1, [-1, 1, -1], 40, 4, 4, 32, 192, 28, 144, unk, unk, unk *],
    [* 476, 1, [1, -1, -1], 40, 4, 4, 20, 180, 26, 132, unk, unk, unk *],
    [* 481, -1, [1, 1], 16, 4, 4, 106, 282, 37, 172, unk, unk, unk *],
    [* 481, -1, [-1, -1], 16, 4, 4, 90, 266, 37, 182, unk, unk, unk *],
    [* 485, -1, [1, 1], 20, 14, 14, 46, 204, 24, 92, unk, unk, unk *],
    [* 485, -1, [-1, -1], 20, 14, 14, 18, 176, 24, 112, unk, unk, unk *],
    [* 488, -1, [1, 1], 30, 6, 6, 44, 192, 25, 116, unk, unk, unk *],
    [* 488, -1, [-1, -1], 30, 6, 6, 24, 172, 25, 130, unk, unk, unk *],
    [* 489, 1, [1, 1], 20, 4, 1, 82, 246, 34, 172, unk, unk, unk *],
    [* 489, 1, [-1, -1], 20, 1, 4, 86, 253, 35, 172, unk, unk, unk *],
    [* 492, 1, [1, 1, 1], 20, 24, 0, 44, 204, 24, 104, unk, unk, unk *],
    [* 492, 1, [-1, -1, 1], 20, 0, 24, 88, 272, 34, 140, unk, unk, unk *],
    [* 492, 1, [-1, 1, -1], 20, 24, 0, 20, 180, 26, 134, unk, unk, unk *],
    [* 492, 1, [1, -1, -1], 20, 0, 24, 40, 224, 32, 160, unk, unk, unk *],
    [* 493, -1, [1, 1], 12, 14, 14, 50, 208, 26, 112, unk, unk, unk *],
    [* 493, -1, [-1, -1], 12, 14, 14, 30, 188, 26, 126, unk, unk, unk *],
    [* 497, 1, [1, 1], 24, 6, 6, 18, 188, 25, 124, unk, unk, unk *],
    [* 497, 1, [-1, -1], 24, 6, 6, 102, 272, 39, 196, unk, unk, unk *]
  *];
  if #Discriminants ne 0 then
    return [* el : el in table | el[1] in Discriminants *];
  end if;
  return table;
end intrinsic;

intrinsic vdGTable( : Discriminants := []) -> List
  {Same signatures as vanderGeerTable.}
  return vanderGeerTable( : Discriminants := Discriminants);
end intrinsic;
