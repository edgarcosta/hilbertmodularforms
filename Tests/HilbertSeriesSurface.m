
// This test uses Prop. VIII.1.1 in vdG
procedure test_level_1(D, bb)
    F := QuadraticField(D);
    ZF := Integers(F);
    N := 1*ZF;

    Gamma := Gamma0(N,bb);
    
    hilb<t> := HilbertSeries(Gamma);

    if (D eq 5) then
	m := (1+t^10)*(1-t)^(-1)*(1-t^3)^(-1)*(1-t^5)^(-1);
	assert hilb eq m;
	return;
    end if;
    
    if (D eq 12) then
	if (Genus(bb) eq [1,1]) then
	    m := (1-t^6)*(1-t^8)*(1-t)^(-1)*(1-t^2)^(-1);
	    m *:= (1-t^3)^(-2)*(1-t^4)^(-1);
	    assert hilb eq m;
	    return;
	end if;
	if (Genus(bb) eq [-1,-1]) then
	    m := (1-t^4)*(1-t^10)*(1-t)^(-1)*(1-t^2)^(-2);
	    m *:= (1-t^3)^(-1)*(1-t^5)^(-1);
	    assert hilb eq m;
	    return;
	end if;
    end if;
    
    chi :=  ArithmeticGenus(Gamma);
    h := NumberOfCusps(Gamma);
    ecd := EllipticPointData(Gamma);
    has_a3plus, a3plus := IsDefined(ecd, <3,1,1>);
    if not has_a3plus then
	a3plus := 0;
    end if;
    vol := VolumeOfFundamentalDomain(Gamma);
    b := [1, chi+h-3, 2*vol - chi - 1/3*a3plus - h + 3];
    b cat:= [2*vol + 2/3*a3plus - 2] cat Reverse(b);
    
    m := &+[b[i+1]*t^i : i in [0..6]];
    m *:= (1-t)^(-2)*(1-t^3)^(-1);
    assert hilb eq m;
    return;
end procedure;

procedure test_level_1_up_to(D)
    printf "testing d = ";
    ds := [d : d in [1..D] | IsFundamentalDiscriminant(d)];
    for d in ds do
	printf "%o ", d;
	F := QuadraticField(d);
	M := GradedRingOfHMFs(F,1);
	for bb in NarrowClassGroupReps(M) do
	    test_level_1(d,bb);
	end for;
    end for;
    return;
end procedure;

test_level_1_up_to(500);
