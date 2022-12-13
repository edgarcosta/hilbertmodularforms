
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

procedure MaybePrint(x)
    if Print then print x; end if;
end procedure;

/*****************************************************************************/
/* Testing IdealToModule */

procedure TestIdealToModule()
    F := RandomField();
    ss := RandomFracIdl(F);
    a := RandomElt(ss);
    r := IdealToModule(a, ss);
    assert Eltseq(r) eq [a];
    MaybePrint(a);
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
    MaybePrint(a);
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
    MaybePrint([a,b]);
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
    MaybePrint(x);
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
    MaybePrint(x);
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
    MaybePrint(list);
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
end for;

printf "Done\n";
