intrinsic EllipticPointCounts(Gamma::StupidCongruenceSubgroup) -> Assoc
{Returns an associative array a such that a[<n,e1,e2>] is the number of points of order n and rotation type <e1,e2>.}
    assert Discriminant(Integers(Field(Gamma))) notin [5,8,12];
    cnt := CountEllipticPoints(Gamma);
    F := Field(Gamma);
    _<x> := PolynomialRing(F);
    a := AssociativeArray();
    // sig := Automorphisms(F)[2];
    for t_n in Keys(cnt) do
	t, n := Explode(t_n);
	/*
	p := x^2+t*x+n;
	if (sig(t) ne t) or (sig(n) ne n) then
	    p *:= x^2+sig(t)*x+sig(n);
	end if;
	is_cyc, ell_order := IsCyclotomicPolynomial(ChangeRing(p, Rationals()));
	assert is_cyc;
	if IsEven(ell_order) then
	    ell_order div:= 2;
	end if;
       */
	K<zeta> := ext<F|x^2+t*x+n>;
	// very inefficient, but at least works
	ell_order := 1;
	while (zeta^ell_order notin F) do
	    ell_order +:= 1;
	end while;
	
	// get options for the rotation factors
	U, mU := UnitGroup(Integers(ell_order));
	qU, pi := quo<U | (-1)@@mU>;
	// !! TODO : needs to sort them according to the 
	// order of the real embeddings of F
	rot_factor := Reverse(Sort([mU(g@@pi) : g in qU]));
	// for now we are only doing surfaces
	assert #rot_factor le 2;
	if rot_factor eq [1] then
	    rot_factor := [1,1];
	end if;
	// check which signs occur (CM types)
	is_unr := IsUnramified(K);
	if is_unr then
	    sign := ArtinSymbol(Integers(K), Component(Gamma));
	    if (sign eq 1) then 
		if not IsDefined(a, <ell_order, rot_factor[1], rot_factor[2]>) then
		    a[<ell_order, rot_factor[1], rot_factor[2]>] := 0;
		end if;
		a[<ell_order, rot_factor[1], rot_factor[2]>] +:= cnt[t_n];
	    else
		if not IsDefined(a, <ell_order, ell_order-rot_factor[1], rot_factor[2]>) then
		    a[<ell_order, ell_order-rot_factor[1], rot_factor[2]>] := 0;
		end if;
		a[<ell_order, ell_order-rot_factor[1], rot_factor[2]>] +:= cnt[t_n];
	    end if;
	else
	    num := Integers()!cnt[t_n];
	    assert IsEven(num);
	    if not IsDefined(a, <ell_order, rot_factor[1], rot_factor[2]>) then
		a[<ell_order, rot_factor[1], rot_factor[2]>] := 0;
	    end if;
	    if not IsDefined(a, <ell_order, ell_order-rot_factor[1], rot_factor[2]>) then
		a[<ell_order, ell_order-rot_factor[1], rot_factor[2]>] := 0;
	    end if;
	    a[<ell_order, rot_factor[1], rot_factor[2]>] +:= num div 2;
	    a[<ell_order, ell_order-rot_factor[1], rot_factor[2]>] +:= num div 2;
	end if;
    end for;
    
    return a;
end intrinsic;

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
  // a2, a3_plus, a3_minus := get_elliptic_counts(Gamma);
  a := EllipticPointCounts(Gamma);
  // a2 := a[<2,1,1>];
  // a3_plus := a[<3,1,1>];
  // a3_minus := a[<3,2,1>];
  elliptic := 0;
  for ell_type in Keys(a) do 
      n := ell_type[1];
      // This is ad-hoc for surfaces
      if ell_type[2] eq 1 then
	  len := 1;  
      elif ell_type[2] eq n-1 then
	  len := n-1;
      elif n eq 5 then
	  assert ell_type[2] in [2,3];
	  len := 2;
      elif n eq 12 then
	  assert ell_type[2] eq 5;
	  len := 3;
      end if;
      elliptic +:= a[ell_type] * (len + (n-1)/n);
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
  a := EllipticPointCounts(Gamma);
  a2 := a[<2,1,1>];
  a3_plus := a[<3,1,1>];
  a3_minus := a[<3,2,1>];
  // a2, a3_plus, a3_minus := get_elliptic_counts(Gamma);
  
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
