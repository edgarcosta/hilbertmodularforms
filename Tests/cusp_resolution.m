
printf "Test computation of change-of-cusp matrices...\n";
//Test change of cusp matrices: example where class group of F is nontrivial
F := QuadraticField(79);
ZF := Integers(F);
G, lift := ClassGroup(ZF);
idreps := [lift(x) : x in G];
id := idreps[2];
alpha, beta := Explode([F!x : x in Generators(id)]);
//id is a prime above 3. Normalize that cusp for level 3
n := 3*ZF;
alpha1, beta1 := NormalizeCusp(F, F!alpha, F!beta, n);
//Choose nonprincipal ideal b, prime to n
b := Factorization(5*ZF)[1][1];

assert IsCoprimeFracIdl(b, n);
assert not IsPrincipal(b);
assert alpha1/beta1 eq alpha/beta;
assert alpha1 in ZF and beta1 in ZF;
assert IsCoprimeFracIdl(alpha1*ZF, n) or IsCoprimeFracIdl(beta1*ZF, n);
assert IsNormalizedCusp(F, alpha1, beta1, n);

g := CuspChangeMatrix(F, b, alpha1, beta1);
I := alpha1*ZF + beta1*b^-1;
assert g[1,1] in I^-1;
assert g[1,2] in I^-1*b^-1;
assert g[2,1] in I*b;
assert g[2,2] in I;
assert Determinant(g) eq 1;
assert g[2,1]*alpha1 + g[2,2]*beta1 eq 0;
assert IsNormalizedCuspChangeMatrix(F, b, n, g);


//-----------------------------------------------//

printf "Compute resolution of cusp at infinity following the examples in Van der Geer...";
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
L := CuspResolutionIntersections(F, 1*ZF, 2*ZF, F!1, F!0: GammaType:="Gamma");
test := [-3,-3,-3];
assert EqUpToCyclicPermutation(L, test);

//p.193: Same field, Gamma(3)
L := CuspResolutionIntersections(F, 1*ZF, 3*ZF, F!1, F!0: GammaType:="Gamma");
test := [-3,-3,-3,-3];
assert EqUpToCyclicPermutation(L, test);

//p.195: Discriminant 8, Level Gamma(p7)
F := QuadraticField(8);
ZF := Integers(F);
p7 := Decomposition(ZF, 7)[1][1];
L := CuspResolutionIntersections(F, 1*ZF, p7, F!1, F!0: GammaType:="Gamma");
test := [-2,-4,-2,-4,-2,-4];
assert EqUpToCyclicPermutation(L, test);

//p.197: Discriminant 13, not quite Gamma(2) but close
F := QuadraticField(13);
ZF := Integers(F);
p := 2*ZF;
L := CuspResolutionIntersections(F, 1*ZF, p, F!1, F!0: GammaType:="GammaP");
test := RepeatSequence([-2,-5,-2], 3); //this is a typo in the book: quadratic number with periodic continued fraction [2,3,2] lies in field of discriminant 21, not 13
assert EqUpToCyclicPermutation(L, test);

//p.198: Discriminant 17, level Gamma(2)
F := QuadraticField(17);
ZF := Integers(F);
p := 2*ZF;
L := CuspResolutionIntersections(F, 1*ZF, p, F!1, F!0: GammaType:="Gamma");
test := [-2,-3,-5,-3,-2];
assert EqUpToCyclicPermutation(L, test);

//p.199: Discriminant 24, level Gamma(3+sqrt(6))
F := QuadraticField(24);
ZF := Integers(F);
p := (3 + SquareRoot(ZF!6))*ZF;
L := CuspResolutionIntersections(F, 1*ZF, p, F!1, F!0: GammaType:="Gamma");
test := RepeatSequence([-2,-2,-2,-4], 2);
assert EqUpToCyclicPermutation(L, test);

//p.201: Discriminant 40, level Gamma(p2)
F := QuadraticField(40);
ZF := Integers(F);
p := Factorization(2*ZF)[1][1];
L := CuspResolutionIntersections(F, 1*ZF, p, F!1, F!0: GammaType:="Gamma");
test := [-2,-3,-4,-3];
assert EqUpToCyclicPermutation(L, test);

//-----------------------------------------------//

printf "Compute resolution of cusps in the case of Gamma1";

//Example with two cusps for Gamma(1)
K<sqrt5> := QuadraticField(5);
ZK<phi> := Integers(K);
p := PrimeIdealsOverPrime(K, 31)[1];
cusps := Cusps(p, 1*ZK : GammaType := "Gamma1");
cusps0 := Cusps(p, 1*ZK: GammaType := "Gamma0");
assert [Eltseq(v): v in cusps] eq [Eltseq(v): v in cusps0];

//Get coordinates of cusps
alpha1, beta1 := Explode(Coordinates(cusps[1]));
alpha2, beta2 := Explode(Coordinates(cusps[2]));

//Normalize
alpha1, beta1 := NormalizeCusp(K, alpha1, beta1, p);
alpha2, beta2 := NormalizeCusp(K, alpha2, beta2, p);

g1 := CuspChangeMatrix(K, 1*ZK, alpha1, beta1);
g2 := CuspChangeMatrix(K, 1*ZK, alpha2, beta2);

b := 1*ZK;
TestCuspChangeMatrix(K, b, p, alpha1, beta1: GammaType:="Gamma0");
L := CuspResolutionIntersections(K, b, p, alpha1, beta1: GammaType:="Gamma0"); L;
TestCuspChangeMatrix(K, b, p, alpha2, beta2: GammaType:="Gamma0");
L := CuspResolutionIntersections(K, b, p, alpha2, beta2: GammaType:="Gamma0"); L;
TestCuspChangeMatrix(K, b, p, alpha1, beta1: GammaType:="Gamma1");
L := CuspResolutionIntersections(K, b, p, alpha1, beta1: GammaType:="Gamma1"); L;
TestCuspChangeMatrix(K, b, p, alpha2, beta2: GammaType:="Gamma1");
L := CuspResolutionIntersections(K, b, p, alpha2, beta2: GammaType:="Gamma1"); L;

//Try a higher, composite level
q := PrimeIdealsOverPrime(K, 5)[1];
n := p^2*q^2;
for T in ["Gamma0", "Gamma1"] do
    cusps := Cusps(n, 1*ZK: GammaType := T);
    for c in cusps do
	print "Cusp number", Index(cusps, c);
	alpha, beta := Explode(Coordinates(c));
	alpha, beta := NormalizeCusp(K, alpha, beta, n);
	print alpha, beta, Valuation(alpha,p), Valuation(beta,p), Valuation(alpha, q), Valuation(beta, q);
	TestCuspChangeMatrix(K, b, n, alpha, beta: GammaType:=T);
	L := CuspResolutionIntersections(K, b, n, alpha, beta: GammaType:=T);
    end for;
end for;

//A final test in the case Gamma0: Van der Geer, Zagier, "The Hilbert
//modular group for the field QQ(sqrt(13)), p.121
K<sqrt13> := QuadraticField(13);
ZK := Integers(K);
p := 2*ZK;
cc := Cusps(p, 1*ZK: GammaType:="Gamma0");
assert #cc eq 2;
for i in [1..#cc] do
    alpha, beta := Explode(Coordinates(cc[i]));
    alpha, beta := NormalizeCusp(K, alpha, beta, p);
    L := CuspResolutionIntersections(K, 1*ZK, p, alpha, beta: GammaType:="Gamma0");
    assert EqUpToCyclicPermutation(L, [-2,-5,-2]);
end for;
    

return true;
