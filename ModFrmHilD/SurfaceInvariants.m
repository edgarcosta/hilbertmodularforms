function get_elliptic_counts(Gamma)
    assert Discriminant(Integers(Field(Gamma))) notin [5,8,12];
    cnt := CountEllipticPoints(Gamma);
    a2 := &+([0] cat [cnt[k] : k in Keys(cnt) | k[1] eq 0]);
    a3_keys := [k : k in Keys(cnt) | k[1] in [-1,1]];
    a3 := &+([0] cat [cnt[k] : k in a3_keys]);
    a2 := Integers()!a2;
    a3 := Integers()!a3;
    F := Field(Gamma);
    _<x> := PolynomialRing(F);
    a3_plus := 0;
    for t_n in a3_keys do
	t, n := Explode(t_n);
	K := ext<F|x^2+t*x+n>;
	is_unr := IsUnramified(K);
	if is_unr then
	    sign := ArtinSymbol(Integers(K), Component(Gamma));
	    if (sign eq 1) then 
		a3_plus +:= cnt[t_n];
	    end if;
	else
	    num := Integers()!cnt[t_n];
	    assert IsEven(num);
	    a3_plus +:= num div 2;
	end if;
    end for;
    return a2, a3_plus, a3 - a3_plus;
end function;

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
  a2, a3_plus, a3_minus := get_elliptic_counts(Gamma);
  elliptic := a2 * (1 + 1/2) + a3_plus * (1 + 2/3) + a3_minus * (2 + 2/3);
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
  a2, a3_plus, a3_minus := get_elliptic_counts(Gamma);
  
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
