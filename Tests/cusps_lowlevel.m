
printf "Testing low-level cusp code...\n";
SetDebugOnError(true);

MaxD := 100;
MaxNorm := 100;
MaxCoefs := 100;
NbTests := 50;
Print := true;

function RandomField()
    D := Random(MaxD);
    F := QuadraticField(D);
    if F eq Rationals() then
        F := RationalsAsNumberField();
    end if;
    return F;
end function;

function RandomIntegralIdl(F)
    ZF := Integers(F);
    all_ideals := IdealsUpTo(MaxNorm, ZF);
    n := Random(all_ideals);
    return n;
end function;

function RandomFracIdl(F)
    ZF := Integers(F);
    all_ideals := IdealsUpTo(MaxNorm, ZF);
    n := Random(all_ideals);
    d := Random(all_ideals);
    b := Random([true,false]);
    if b then
        return n; //Integral ideal
    else
        return n * d^(-1);
    end if;
end function;

function RandomPrimes(F, nb)
    primes := PrimesUpTo(nb+100);
    ZF := Integers(F);
    list := [];
    for i:=1 to nb do
        p := Random(primes);
        Append(~list, Factorization(p*ZF)[1][1]);
        primes := [q: q in primes| q ne p];
    end for;
    return list;
end function;

function RandomElt(id)
    return Random(id, MaxCoefs);
end function;

/*****************************************************************************/
/* Testing IdealToModule */

procedure TestIdealToModule()
    F := RandomField();
    ss := RandomFracIdl(F);
    a := RandomElt(ss);
    r := IdealToModule(a, ss);
    assert Eltseq(r) eq [a];
    //This tests both RngOrdElt and FldElt version depending on whether ss is integral or not  
end procedure;

/*****************************************************************************/
/* Testing ModuleToIdeal */

procedure TestModuleToIdeal()
    F := RandomField();
    ss := RandomFracIdl(F);
    a := RandomElt(ss);
    r := IdealToModule(a, ss);
    a2 := ModuleToIdeal(r);
    assert a2 eq a;
end procedure;

/*****************************************************************************/
/* Testing ReduceModuloIdeal */

procedure TestReduceModuloIdeal()
    F := RandomField();
    I := RandomFracIdl(F);
    J := RandomIntegralIdl(F) * I; //Fractional ideal included in I
    a := RandomElt(I);
    b := a + RandomElt(J);
    r := ReduceModuloIdeal(a, I, J);
    s := ReduceModuloIdeal(b, I, J);
    assert r in I;
    assert s in I;
    assert r eq s;
end procedure;

/*****************************************************************************/
/* Testing FindEltWithValuations */

procedure TestFindEltWithValuations()
    F := RandomField();
    ZF := Integers(F);
    nb := Random(10);
    ps := RandomPrimes(F, nb);
    vs := [Random(-5,5): i in [1..nb]];
    x := FindEltWithValuations(F, ps, vs);
    
    ss := 1*ZF;
    for i:=1 to nb do
        ss *:= ps[i] ^ vs[i];
    end for;
    assert x in ss;
    assert IsIntegral(x * ss^(-1));
    for p in ps do
        assert Gcd(x * ss^(-1), p) eq 1*ZF;
    end for;
end procedure;

/*****************************************************************************/
/* Testing GeneratorOfQuotientModuleCRT */

procedure TestGeneratorOfQuotientModuleCRT()
    F := RandomField();    
    ss := RandomFracIdl(F);
    MM := RandomIntegralIdl(F);
    x := GeneratorOfQuotientModuleCRT(ss, MM);
    primes := [p[1]: p in Factorization(MM)];
    
    assert x in ss;
    for p in primes do
        assert not x in ss*p;
    end for;
end procedure;

/*****************************************************************************/
/* Testing GeneratorsOfQuotientModule */

procedure TestGeneratorsOfQuotientModule()
    F := RandomField();    
    ss := RandomFracIdl(F);
    MM := RandomIntegralIdl(F);
    list := GeneratorsOfQuotientModule(ss, MM);
    primes := [p[1]: p in Factorization(MM)];

    assert #list eq #UnitGroup(quo<Integers(F)|MM>);
    
    for x in list do    
        assert x in ss;
        for p in primes do
            assert not x in ss*p;
        end for;
    end for;
end procedure;

/*****************************************************************************/
/* Testing GeneratorsOfQuotientModuleModuloTotallyPositiveUnits */

procedure TestGeneratorsOfQuotientModuleModuloTotallyPositiveUnits()
    F := RandomField();    
    ss := RandomFracIdl(F);
    MM := RandomIntegralIdl(F);    
    list := GeneratorsOfQuotientModuleModuloTotallyPositiveUnits(ss, MM);
    //Check they are indeed generators of module
    primes := [p[1]: p in Factorization(MM)];
    for x in list do    
        assert x in ss;
        for p in primes do
            assert not x in ss*p;
        end for;
    end for;
    //Get order n of totally positive unit
    eps := FundamentalUnitTotPos(F);
    u := eps;
    n:= 1;
    while not u-1 in MM do
        u *:= eps;
        n +:= 1;
    end while;
    //Check size of list + action of epsilon indeed gets everything
    assert #list eq #UnitGroup(quo<Integers(F)|MM>)/n;
    all := SequenceToSet(list);
    for i:=1 to n-1 do
        new := SequenceToSet([eps^i * x: x in list]);
        assert new meet all eq {};
        all := all join new;
    end for;
    assert #all eq #UnitGroup(quo<Integers(F)|MM>);
end procedure;

/*****************************************************************************/
/* Testing MakePairsForQuadruple */

procedure TestMakePairsForQuadruple()
    F := RandomField();
    if not Degree(F) eq 2 then return; end if;
    //if not #NarrowClassGroup(F) eq 1 then return; end if;
    NN := RandomIntegralIdl(F);
    //if not #Factorization(NN) eq 1 then return; end if;
    MM := Random(Divisors(NN));
    GammaType := Random(["Gamma0", "Gamma1"]);

    count := 0;
    NCl, mNCl := NarrowClassGroup(F);
    Cl, mCl := ClassGroup(F);
    for bbb in NCl do
        for sss in Cl do
            ss := mCl(sss);
            bb := mNCl(bbb);
            pairs := MakePairsForQuadruple(NN, bb, ss, MM: GammaType := GammaType);
            primes_check_a := [p[1]: p in Factorization(MM)];
            primes_check_c := [p[1]: p in Factorization(NN/MM)];
            
            //Check a,c land in correct ideals
            for i:=1 to #pairs do
                a, c := Explode(pairs[i]);
                assert a in ss;
                for p in primes_check_a do
                    assert not a in ss*p;
                end for;
                assert c in ss*bb*MM;
                for p in primes_check_c do
                assert not c in ss*bb*MM*p;
                end for;
            end for;
            printf "Adding %o\n", #pairs;
            count +:= #pairs;
        end for;
    end for;
    
    //Check cardinality according to Dasgupta--Kakde
    if Degree(F) eq 1 then infty:=[1]; else infty:=[1,2]; end if;
    ZF := Integers(F);
    Gm, m1 := RayClassGroup(MM, infty);
    Gnm, m2 := RayClassGroup(NN/MM, infty);
    Gn, m := RayClassGroup(NN, infty);
    Cln, mm := RayClassGroup(NN);
    G, i1, i2, p1, p2 := DirectSum(Gm, Gnm);
    gens := [];
    if GammaType eq "Gamma1" then
        for idl in Gn do
            x := m(idl);
            if IsId(x@@mm) then            
                Append(~gens, i1(x@@m1) - i2(x@@m2));
            end if;
        end for;
    else
        for idl in Gn do
            x := m(idl);
            if IsId(x@@mCl) then
                Append(~gens, i1(x@@m1) - i2(x@@m2));
            end if;
        end for;
    end if;
    Q := quo<G|gens>;
    print count, #Q, #ClassGroup(F), #NarrowClassGroup(F), F, NN, MM, GammaType, Factorization(NN);
    assert count eq #Q;
end procedure;

/*****************************************************************************/
/* Testing CuspQuadruples */

procedure TestCuspQuadruples()
    F := RandomField();
    NN := RandomIntegralIdl(F);
    if not IsPrime(NN) then return; end if;
    bb := RandomIntegralIdl(F);
    GammaType := "Gamma1"; //Random(["Gamma0", "Gamma1"]);
    quads := CuspQuadruples(NN, bb: GammaType := GammaType);
    ZF := Integers(F);
    
    // Check each quadruple is well-formed
    for q in quads do
        ss := q[1];
        MM := q[2];
        a, c := Explode(q[3]);
        assert NN subset MM; //MM divides NN
        primes_check_a := [p[1]: p in Factorization(MM)];
        primes_check_c := [p[1]: p in Factorization(NN/MM)];
        assert a in ss;
        for p in primes_check_a do
            assert not a in ss*p;
        end for;
        assert c in ss*bb*MM;
        for p in primes_check_c do
            assert not c in ss*bb*MM*p;
        end for;
    end for;
    //This tests the number of quadruples using Eisenstein dimensions
    print F, NN, Factorization(NN), GammaType, #NarrowClassGroup(F);
    //if Degree(F) gt 1 then assert CuspSanityCheck(NN: GammaType := GammaType); end if;
end procedure;

/*****************************************************************************/
/* Testing CuspLiftFirstCoordinate */

procedure TestCuspLiftFirstCoordinate()
    F := RandomField();
    NN := RandomIntegralIdl(F);
    bb := RandomIntegralIdl(F);
    GammaType := Random(["Gamma0", "Gamma1"]);
    quads := CuspQuadruples(NN, bb: GammaType := GammaType);
    ZF := Integers(F);

    for q in quads do
        ss := q[1];
        MM := q[2];
        a_bar, c := Explode(q[3]);
        a := CuspLiftFirstCoordinate(a_bar, c, ss, MM, NN, bb);
        assert a in ss;
        assert c in ss*bb*MM;        
        assert Gcd(c*ZF, ss*bb*NN) eq ss*bb*MM;
        assert a*ZF + c*bb^(-1) eq ss;
    end for;
end procedure;

/*****************************************************************************/
/* Run tests */

for i:=1 to NbTests do
    TestIdealToModule();
    TestModuleToIdeal();
    TestReduceModuloIdeal();
    TestFindEltWithValuations();
    TestGeneratorOfQuotientModuleCRT();
    TestGeneratorsOfQuotientModule();
    TestGeneratorsOfQuotientModuleModuloTotallyPositiveUnits();
    TestMakePairsForQuadruple();
    TestCuspQuadruples();
    TestCuspLiftFirstCoordinate();
end for;

printf "Done\n";
