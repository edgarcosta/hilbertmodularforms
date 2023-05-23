procedure testHZDivisor1(Gamma)
    comps1 := GetAllHZComponents(Gamma,1);
    bb := Component(Gamma);
    D := Discriminant(Order(bb));
    if IsPrincipalGenus(bb) then
	assert #comps1 eq 2^(#PrimeDivisors(D) - 1);
    else
	assert #comps1 eq 0;
    end if;
    return;
end procedure;

procedure testHZDivisor2(Gamma)
    comps2 := GetAllHZComponents(Gamma,2);
    bb := Component(Gamma);
    F := BaseField(Gamma);
    frakps := PrimeIdealsOverPrime(F,2);
    has_comps := exists(aa){frakp : frakp in frakps | Genus(frakp) eq Genus(bb)};
    if not has_comps then
	assert #comps2 eq 0;
	return;
    end if;
    D := Discriminant(Order(bb));
     // !! TODO : add the correct number for D = 8
    assert D ne 8;
    qs := PrimeDivisors(D);
    Dqs := [PrimeDiscriminant(D,q) : q in qs];
    n_comps := &*[1 + KroneckerSymbol(Dq, 2*Norm(aa)) : Dq in Dqs] div 2;
    assert #comps2 eq n_comps;
    return;
end procedure;

procedure testHZDivisor3(Gamma)
    comps3 := GetAllHZComponents(Gamma,3);
    bb := Component(Gamma);
    F := BaseField(Gamma);
    frakps := PrimeIdealsOverPrime(F,3);
    has_comps := exists(aa){frakp : frakp in frakps | Genus(frakp) eq Genus(bb)};
     if not has_comps then
	assert #comps3 eq 0;
	return;
    end if;
    D := Discriminant(Order(bb));
    // !! TODO : add the correct number for D = 12
    assert D ne 12;
    qs := PrimeDivisors(D);
    Dqs := [PrimeDiscriminant(D,q) : q in qs];
    n_comps := &*[1 + KroneckerSymbol(Dq, 3*Norm(aa)) : Dq in Dqs] div 2;
    assert #comps3 eq n_comps;
    return;
end procedure;

procedure testHZDivisor4(Gamma)
    comps4 := GetAllHZComponents(Gamma,4);
    bb := Component(Gamma);
    if not IsPrincipalGenus(bb) then
	assert #comps4 eq 0;
	return;
    end if;
    D := Discriminant(Order(bb));
    // !! TODO : add the correct number for D = 8
    assert D ne 8;
    t := #PrimeDivisors(D);
    if IsOdd(D) then
	n_comps := 2^(t-1);
    else
	n_comps := 2^(t-2);
    end if;
    assert #comps4 eq n_comps;
    return;
end procedure;

procedure testHZDivisor9(Gamma)
    comps9 := GetAllHZComponents(Gamma,9);
    bb := Component(Gamma);
    if not IsPrincipalGenus(bb) then
	assert #comps9 eq 0;
	return;
    end if;
    D := Discriminant(Order(bb));
    // !! TODO : add the correct number for D = 12
    assert D ne 12;
    n_comps := 2^(#PrimeDivisors(D) - 1);
    assert #comps9 eq n_comps;
    return;
end procedure;

procedure testHZDivisors(Gamma)
    // testing the number of components for various known cases
    testHZDivisor1(Gamma);
    bb := Component(Gamma);
    D := Discriminant(Order(bb));
    if (D ne 8) then
	testHZDivisor2(Gamma);
	testHZDivisor4(Gamma);
    end if;
    if (D ne 12) then
	testHZDivisor3(Gamma);
	testHZDivisor9(Gamma);
    end if;
    return;
end procedure;

ds := [d : d in [2..500] | IsFundamentalDiscriminant(d)];
// DN_bound := 500;
num_attempts := 10;

for _ in [1..num_attempts] do
    d := Random(ds);
    F := QuadraticField(d);
    ZF := Integers(F);
    ncg, ncg_map := NarrowClassGroup(F);
    b := Random(ncg);
    B := ncg_map(b);
    // We are choosing a representative coprime to the discriminant
    a := CoprimeNarrowRepresentative(B,d*ZF);
    assert IsTotallyPositive(a);
    assert a*B + d*ZF eq 1*ZF;
    B := a*B;    
    printf "(%o;%o),", d, IdealOneLine(B);
    G_SL := CongruenceSubgroup("SL", "Gamma0", F, 1*ZF, B);
    testHZDivisors(G_SL);
end for;

// Print newline.
print "";


/* long test

for d in ds do
    F := QuadraticField(d);
    ZF := Integers(F);
    ncg, ncg_map := NarrowClassGroup(F);
    for b in ncg do
    	B := ncg_map(b);
	// We are choosing a representative coprime to the discriminant
	a := CoprimeNarrowRepresentative(B,d*ZF);
	assert IsTotallyPositive(a);
	assert a*B + d*ZF eq 1*ZF;
	B := a*B;    
	printf "(%o;%o),", d, IdealOneLine(B);
	G_SL := CongruenceSubgroup("SL", "Gamma0", F, 1*ZF, B);
	testHZDivisors(G_SL);
    end for;
end for;

*/
