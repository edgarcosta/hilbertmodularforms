intrinsic EulerNumber(Gamma::GrpHilbert) -> RngIntElt
{}
  // for these fields there are additional orders of points
  // At the moment we do not handle them. 
  F := BaseField(Gamma);
  assert Discriminant(Integers(F)) notin [8,12];
 
  cusps := Cusps(Level(Gamma), Component(Gamma) : GammaType := "Gamma0");
  vol := VolumeOfFundamentalDomain(Gamma);
  // get cusp contribution
  l := 0;
  for cusp in cusps do
      alpha, beta := NormalizeCusp(F, cusp[3][1], cusp[3][2], Level(Gamma));
      L,n := CuspResolutionIntersections(F, cusp[1], Level(Gamma), alpha, beta
					: GammaType := GammaType(Gamma));
      l +:= #L * n;
  end for;
  
  // get elliptic points contribution
  a := CountEllipticPoints(Gamma);
  
  elliptic := 0;
  for n in Keys(a) do 
      for rot_factor in Keys(a[n]) do
	  // This is ad-hoc for surfaces
	  if rot_factor[1] eq 1 then
	      len := 1;  
	  elif rot_factor[1] eq n-1 then
	      len := n-1;
	  elif n eq 5 then
	      assert rot_factor[1] in [2,3];
	      len := 2;
	  elif n eq 12 then
	      assert rot_factor[1] eq 5;
	      len := 3;
	  end if;
	  elliptic +:= a[n][rot_factor] * (len + (n-1)/n);
      end for;
  end for;
  // elliptic := a2 * (1 + 1/2) + a3_plus * (1 + 2/3) + a3_minus * (2 + 2/3);
  e := vol + l + elliptic;
  assert IsIntegral(e);
  e := Integers()!e;
  return e;
end intrinsic;

intrinsic K2(Gamma::GrpHilbert) -> RngIntElt
{}
  // for these fields there are additional orders of points
  // At the moment we do not handle them. 
  F := BaseField(Gamma);
  assert Discriminant(Integers(F)) notin [8,12];
  
  cusps := Cusps(Level(Gamma), Component(Gamma) : GammaType := "Gamma0");
  vol := VolumeOfFundamentalDomain(Gamma);
  // get cusp contribution
  cusp_chern := 0;
  for cusp in cusps do
      alpha, beta := NormalizeCusp(F, cusp[3][1], cusp[3][2], Level(Gamma));
      L,n := CuspResolutionIntersections(F, cusp[1], Level(Gamma), alpha, beta
					: GammaType := GammaType(Gamma));
      if (n eq 1) and (#L eq 1) then
	  cusp_chern +:= L[1];
      else
	  cusp_chern +:= n*(&+[2+b : b in L]);
      end if;
  end for;
  // get elliptic points contribution
  a := CountEllipticPoints(Gamma);
  a3_plus := a[3][[1,1]];
  if IsDefined(a,5) then
      a5 := a[5][[2,1]] + a[5][[3,1]];
  else
      a5 := 0;
  end if;
  
  elliptic := a3_plus * (-1/3) + a5 * (-2/5);
  k2 := 2*vol + cusp_chern + elliptic;
  assert IsIntegral(k2);
  k2 := Integers()!k2;
  return k2;
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
