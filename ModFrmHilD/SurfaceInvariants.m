intrinsic EulerNumber(Gamma::StupidCongruenceSubgroup) -> RngIntElt
{}
  // for these fields there are additional orders of points
  // At the moment we do not handle them. 
  F := Field(Gamma);
  assert Discriminant(Integers(F)) notin [5,8,12];
 
  cusps := Cusps(Level(Gamma), Component(Gamma) : GammaType := "Gamma0");
  vol := VolumeOfFundamentalDomain(Gamma);
  // get cusp contribution
  l := 0;
  for cusp in cusps do
      alpha, beta := NormalizeCusp(F, cusp[3][1], cusp[3][2], Level(Gamma));
      L,n := CuspResolutionIntersections(F, cusp[1], Level(Gamma), alpha, beta);
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

intrinsic K2(Gamma::StupidCongruenceSubgroup) -> RngIntElt
{}
  // for these fields there are additional orders of points
  // At the moment we do not handle them. 
  F := Field(Gamma);
  assert Discriminant(Integers(F)) notin [5,8,12];
  
  cusps := Cusps(Level(Gamma), Component(Gamma) : GammaType := "Gamma0");
  vol := VolumeOfFundamentalDomain(Gamma);
  // get cusp contribution
  cusp_chern := 0;
  for cusp in cusps do
      alpha, beta := NormalizeCusp(F, cusp[3][1], cusp[3][2], Level(Gamma));
      L,n := CuspResolutionIntersections(F, cusp[1], Level(Gamma), alpha, beta);
      cusp_chern +:= n*(&+[2+b : b in L]);
  end for;
  // get elliptic points contribution
  // a := EllipticPointCounts(Gamma);
  // a2 := a[<2,1,1>];
  // a3_plus := a[<3,1,1>];
  // a3_minus := a[<3,2,1>];
  // a2, a3_plus, a3_minus := get_elliptic_counts(Gamma);
  a := CountEllipticPoints(Gamma);
  a2 := a[2][[1,1]];
  a3_plus := a[3][[1,1]];
  a3_minus := a[3][[2,1]];
  
  elliptic := a3_plus * (-1/3);
  k2 := 2*vol + cusp_chern + elliptic;
  assert IsIntegral(k2);
  k2 := Integers()!k2;
  return k2;
end intrinsic;

intrinsic ArithmeticGenus(Gamma::StupidCongruenceSubgroup) -> RngIntElt
{}
  chi := K2(Gamma) + EulerNumber(Gamma);
  assert chi mod 12 eq 0;
  return chi div 12;
end intrinsic;

intrinsic Irregularity(Gamma::StupidCongruenceSubgroup) -> RngIntElt
{}
  return 0;
end intrinsic;

intrinsic GeometricGenus(Gamma::StupidCongruenceSubgroup) -> RngIntElt
{}
  return ArithmeticGenus(Gamma)-1;
end intrinsic;

intrinsic HodgeDiamond(Gamma::StupidCongruenceSubgroup) -> RngIntEltt
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
  return [h_1, h_2, h_3, h_4];
end intrinsic;
