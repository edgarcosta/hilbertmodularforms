
//Some randomized testing
SetDebugOnError(true);
//SetSeed(1);

MaxD := 100;
MaxNorm := 5;
MaxCoefs := 5; //Beware of large fundamental units...
NbTests := 500;

function RandomField()
    D := Random(MaxD);
    F := QuadraticField(D);
    if F eq Rationals() then
        F := QuadraticField(79);
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

function RandomNonzero(F)
    x := Random(F, MaxCoefs);
    while x eq 0 do x := Random(F, MaxCoefs); end while;
    return x;
end function;    

procedure TestGeneratorsOfGMV()
    F := RandomField();
    M := RandomFracIdl(F);
    w := FundamentalUnitTotPos(F);
    V := w^(Random([1..10]));
    gs := NewGeneratorsOfGMV(M, V);
    for i:=1 to 3 do
        x := RandomNonzero(F);
        assert IsInGMV(M, V, x*gs[i]);
    end for;
end procedure;

procedure TestSamplesOfLevelSubgroup()
    F := RandomField();
    n := RandomIntegralIdl(F);
    b := RandomFracIdl(F);
    GammaType := Random(["Gamma0", "Gamma1", "Gamma"]);
    GroupType := Random(["GL2+", "SL2"]);
    gs := SamplesOfLevelSubgroup(b, n: GammaType := GammaType, GroupType := GroupType);
    for i:=1 to #gs do
        x := RandomNonzero(F);
        assert IsInLevelSubgroup(b, n, x*gs[i]: GammaType := GammaType, GroupType := GroupType);
    end for;
end procedure;

procedure TestCuspResolutionMV()
    F := RandomField();
    ZF := Integers(F);
    n := RandomIntegralIdl(F);
    //Sometimes pick n, beta not coprime
    alpha := RandomNonzero(F);
    beta := Random(F, 10);
    if Random([true, false]) then
        x := RandomNonzero(ZF);
        n := x*n;
        beta := x*beta;
    end if;
    //Make b, n coprime, normalize cusp
    b := RandomIntegralIdl(F);
    g := Gcd(b, n);
    n := n/g;
    b := b/g;
    assert IsCoprimeFracIdl(n, b);    
    alpha, beta := NormalizeCusp(b, n, alpha, beta);
    g := CuspChangeMatrix(b, alpha, beta);
    lambda := g[1,1];
    mu := g[1,2];
    I := alpha*ZF + beta*b^(-1);
    assert IsNormalizedCuspChangeMatrix(b, n, g);
    
    GammaType := Random(["Gamma0", "Gamma1", "Gamma"]);
    GroupType := Random(["GL2+", "SL2"]);
    M, V, mx, g := NewCuspResolutionMV(b, n, alpha, beta:
                                       GammaType := GammaType, GroupType := GroupType);
    GMV_gens := NewGeneratorsOfGMV(M, V);
    samples := SamplesOfLevelSubgroup(b, n: GammaType:=GammaType, GroupType:=GroupType);

    if true then
        print "Entering new test";
        print GammaType;
        print GroupType;
        print M;
        print V;
        print g;
        print GMV_gens;
        print samples;
    end if;
    assert g[2,1]*alpha + g[2,2]*beta eq 0;

    test := [g^(-1)*mx^(-1)*y*mx*g: y in GMV_gens];
    print "Now testing:";
    for i:=1 to #GMV_gens do
        print GMV_gens[i];
        gen_mod := mx^(-1) * GMV_gens[i] * mx;
        print test[i];
        print "";
        if not IsInLevelSubgroup(b, n, test[i]: GammaType:=GammaType, GroupType:=GroupType) then
            print "WRONG!";
            error "";
        end if;
    end for;
    test := [g*x*g^(-1): x in samples];
    for i:=1 to #samples do
        print samples[i];
        print test[i];
        print "";
        if test[i][2,1] eq 0 and not IsInGMV(M, V, test[i]) then
            print "WRONG!";
            //error "";
        end if;
    end for;    
end procedure;
    
for i:=1 to NbTests do
    TestGeneratorsOfGMV();
    TestSamplesOfLevelSubgroup();
    TestCuspResolutionMV();
end for;

//---------------------------------------------//

//Test change of cusp matrices: example where class group of F is nontrivial
F := QuadraticField(79);
ZF := Integers(F);
G, lift := ClassGroup(ZF);
idreps := [lift(x) : x in G];
id := idreps[2];

n := 3*ZF;
//Choose nonprincipal ideal b, prime to n
b := Factorization(5*ZF)[1][1];

alpha, beta := Explode([F!x : x in Generators(id)]);
//id is a prime above 3. Normalize that cusp for level 3
alpha1, beta1 := NormalizeCusp(b, n, alpha, beta);

assert IsCoprimeFracIdl(b, n);
assert not IsPrincipal(b);
assert alpha1/beta1 eq alpha/beta;
assert alpha1 in ZF and beta1 in b;
assert IsCoprimeFracIdl(alpha1*ZF, n) or IsCoprimeFracIdl(beta1*ZF, n);
assert IsNormalizedCusp(b, n, alpha1, beta1);

g := CuspChangeMatrix(b, alpha1, beta1);
I := alpha1*ZF + beta1*b^-1;
assert g[1,1] in I^-1;
assert g[1,2] in I^-1*b^-1;
assert g[2,1] in I*b;
assert g[2,2] in I;
assert Determinant(g) eq 1;
assert g[2,1]*alpha1 + g[2,2]*beta1 eq 0;
assert IsNormalizedCuspChangeMatrix(b, n, g);


//-----------------------------------------------//

//Compute resolution of cusp at infinity following the examples in Van
//der Geer, starting p.189

function EqUpToCyclicPermutation(L1, L2)
    n := #L1;
    if n ne #L2 then return false; end if;
    for k := 1 to n do
	if L1 eq L2 then return true; end if;
	L1 := L1[2..n] cat [L1[1]];
    end for;
    return false;
end function;

//p.189: Discriminant 5, level Gamma(2)
F := QuadraticField(5);
ZF := Integers(F);
L, nb := CuspResolutionIntersections(1*ZF, 2*ZF, F!1, F!0:
                                     GammaType:="Gamma", GroupType:="SL2");
test := [-3];
assert EqUpToCyclicPermutation(L, test) and nb eq 3;

//p.193: Same field, Gamma(3)
L, nb := CuspResolutionIntersections(1*ZF, 3*ZF, F!1, F!0:
                                     GammaType:="Gamma", GroupType:="SL2");
test := [-3];
assert EqUpToCyclicPermutation(L, test) and nb eq 4;

//p.195: Discriminant 8, Level Gamma(p7)
F := QuadraticField(8);
ZF := Integers(F);
p7 := Decomposition(ZF, 7)[1][1];
L, nb := CuspResolutionIntersections(1*ZF, p7, F!1, F!0:
                                     GammaType:="Gamma", GroupType:="SL2");
test := [-2,-4];
assert EqUpToCyclicPermutation(L, test) and nb eq 3;

//p.197: Discriminant 13, not quite Gamma(2) but close
F := QuadraticField(13);
ZF := Integers(F);
p := 2*ZF;
L, nb := CuspResolutionIntersections(1*ZF, p, F!1, F!0:
                                     GammaType:="GammaP", GroupType:="SL2");
test := [-2,-5,-2]; //this is a typo in the book: quadratic number with periodic continued fraction [2,3,2] lies in field of discriminant 21, not 13
assert EqUpToCyclicPermutation(L, test) and nb eq 3;

//p.198: Discriminant 17, level Gamma(2)
F := QuadraticField(17);
ZF := Integers(F);
p := 2*ZF;
L, nb := CuspResolutionIntersections(1*ZF, p, F!1, F!0:
                                     GammaType:="Gamma", GroupType:="SL2");
test := [-2,-3,-5,-3,-2];
assert EqUpToCyclicPermutation(L, test) and nb eq 1;

//p.199: Discriminant 24, level Gamma(3+sqrt(6))
//
// Note: We  want the action of SL_2(ZF) on H x H-, or equivalently (p. 165/166),
// we want to take the component to represent the non-trivial element of the narrow
// class group.
F := QuadraticField(24);
ZF := Integers(F);
b := (1 + ZF.2) * ZF; // Component ideal.
assert not HasTotallyPositiveGenerator(b);
p := (3 + SquareRoot(ZF!6))*ZF;
assert IsCoprime(b, p);
L, nb := CuspResolutionIntersections(b, p, F!1, F!0:
                                     GammaType:="Gamma", GroupType:="SL2");
test := [-2,-2,-2,-4];
assert EqUpToCyclicPermutation(L, test) and nb eq 2;

//p.201: Discriminant 40, level Gamma(p2)
F := QuadraticField(40);
ZF := Integers(F);
p := Factorization(2*ZF)[1][1];
L, nb := CuspResolutionIntersections(1*ZF, p, F!1, F!0:
                                     GammaType:="Gamma", GroupType:="SL2");
test := [-2,-3,-4,-3];
assert EqUpToCyclicPermutation(L, test) and nb eq 1;


//A final test in the case Gamma0: Van der Geer, Zagier, "The Hilbert
//modular group for the field QQ(sqrt(13)), p.121
K<sqrt13> := QuadraticField(13);
ZK := Integers(K);
p := 2*ZK;
cc := Cusps(p, 1*ZK: GammaType:="Gamma0"); //This is the same for SL2 and GL2+?
assert #cc eq 2;
for i in [1..#cc] do
    alpha, beta := Explode(Coordinates(cc[i][3]));
    alpha, beta := NormalizeCusp(1*ZK, p, alpha, beta);
    L, nb := CuspResolutionIntersections(1*ZK, p, alpha, beta:
                                         GammaType:="Gamma0", GroupType:="SL2");
    assert EqUpToCyclicPermutation(L, [-2,-5,-2]) and nb eq 1;
end for;

//-----------------------------------------------//

/*
//Example with two cusps for Gamma(1)
K<sqrt5> := QuadraticField(5);
ZK<phi> := Integers(K);
p := PrimeIdealsOverPrime(K, 31)[1];
cusps := Cusps(p, 1*ZK : GammaType := "Gamma1");
cusps0 := Cusps(p, 1*ZK: GammaType := "Gamma0");
assert [Eltseq(v[3]): v in cusps] eq [Eltseq(v[3]): v in cusps0];
b := 1*ZK;

//Get coordinates of cusps
alpha1, beta1 := Explode(Coordinates(cusps[1][3]));
alpha2, beta2 := Explode(Coordinates(cusps[2][3]));

//Normalize
alpha1, beta1 := NormalizeCusp(b, p, alpha1, beta1);
alpha2, beta2 := NormalizeCusp(b, p, alpha2, beta2);

g1 := CuspChangeMatrix(b, alpha1, beta1);
g2 := CuspChangeMatrix(b, alpha2, beta2);

TestCuspChangeMatrix(b, p, alpha1, beta1: GammaType:="Gamma0");
L, nb := CuspResolutionIntersections(b, p, alpha1, beta1: GammaType:="Gamma0");
TestCuspChangeMatrix(b, p, alpha2, beta2: GammaType:="Gamma0");
L, nb := CuspResolutionIntersections(b, p, alpha2, beta2: GammaType:="Gamma0");
TestCuspChangeMatrix(b, p, alpha1, beta1: GammaType:="Gamma1");
L, nb := CuspResolutionIntersections(b, p, alpha1, beta1: GammaType:="Gamma1");
TestCuspChangeMatrix(b, p, alpha2, beta2: GammaType:="Gamma1");
L, nb := CuspResolutionIntersections(b, p, alpha2, beta2: GammaType:="Gamma1");

v := false;
//Try a higher, composite level
q := PrimeIdealsOverPrime(K, 5)[1];
n := p^2*q^2;
for T in ["Gamma0", "Gamma1"] do
    cusps := Cusps(n, 1*ZK: GammaType := T);
    for c in cusps do
	if v then print "Cusp number", Index(cusps, c); end if;
	alpha, beta := Explode(Coordinates(c[3]));
	alpha, beta := NormalizeCusp(b, n, alpha, bet);
	if v then print alpha, beta, Valuation(alpha,p), Valuation(beta,p), Valuation(alpha, q), Valuation(beta, q); end if;
	TestCuspChangeMatrix(b, n, alpha, beta: GammaType:=T);
	L := CuspResolutionIntersections(b, n, alpha, beta: GammaType:=T);
    end for;
end for;
*/
