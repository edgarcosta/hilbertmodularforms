
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

g := CuspChangeMatrix(F, b, F!alpha, F!beta);
I := alpha*ZF + beta*b^-1;

assert g[1,1] in I^-1;
assert g[1,2] in I^-1*b^-1;
assert g[2,1] in I*b;
assert g[2,2] in I;
assert g[2,1]*alpha + g[2,2]*beta eq 0;

I := alpha1*ZF + beta1*b^-1;
y := alpha1/beta1;
denom := Gcd(y*ZF, 1*ZF)^-1;
assert IsCoprimeFracIdl(I, n);
assert IsCoprimeFracIdl(denom, n);

x := CuspCRT(F, I, n, y);
assert x in I;

g := NormalizedCuspChangeMatrix(F, b, alpha1, beta1, n);
assert g[1,1] in I^-1;
assert g[1,2] in I^-1*b^-1;
assert g[2,1] in I*b;
assert g[2,2] in I;
assert Determinant(g) eq 1;

R<V,M> := PolynomialRing(F, 2);
stab_elt := Matrix(R, 2, 2, [V, M, 0, 1]);
conj := g*stab_elt*g^-1;

//conj should be of the form [xm+1, y(v-1)+zm; xm, y(v-1)+zm+1] mod n with x invertible
assert F!Coefficient(conj[2,1], V, 1) in I*b*n;
assert F!Coefficient(Coefficient(conj[2,1], V, 0), M, 0) in I*b*n;
assert F!Coefficient(conj[1,1]-1, V, 1) in I^-1*n;
assert F!Coefficient(Coefficient(conj[1,1]-1, V, 0), M, 0) in I^-1*n;

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
L := CuspResolutionIntersections(F, 1*ZF, 2*ZF, F!1, F!0);
test := [-3,-3,-3];
assert EqUpToCyclicPermutation(L, test);

//p.193: Same field, Gamma(3)
L := CuspResolutionIntersections(F, 1*ZF, 3*ZF, F!1, F!0);
test := [-3,-3,-3,-3];
assert EqUpToCyclicPermutation(L, test);

//p.195: Discriminant 8, Level Gamma(p7)
F := QuadraticField(8);
ZF := Integers(F);
p7 := Decomposition(ZF, 7)[1][1];
L := CuspResolutionIntersections(F, 1*ZF, p7, F!1, F!0);
test := [-2,-4,-2,-4,-2,-4];
assert EqUpToCyclicPermutation(L, test);

//p.197: Discriminant 13, not quite Gamma(2) but close
F := QuadraticField(13);
ZF := Integers(F);
p := 2*ZF;
L := CuspResolutionIntersections(F, 1*ZF, p, F!1, F!0: flag:=2);
test := RepeatSequence([-2,-5,-2], 3); //this is a typo in the book: quadratic number with periodic continued fraction [2,3,2] lies in field of discriminant 21, not 13
assert EqUpToCyclicPermutation(L, test);

//p.198: Discriminant 17, level Gamma(2)
F := QuadraticField(17);
ZF := Integers(F);
p := 2*ZF;
L := CuspResolutionIntersections(F, 1*ZF, p, F!1, F!0);
test := [-2,-3,-5,-3,-2];
assert EqUpToCyclicPermutation(L, test);

//p.199: Discriminant 24, level Gamma(3+sqrt(6))
F := QuadraticField(24);
ZF := Integers(F);
p := (3 + SquareRoot(ZF!6))*ZF;
L := CuspResolutionIntersections(F, 1*ZF, p, F!1, F!0);
test := RepeatSequence([-2,-2,-2,-4], 2);
assert EqUpToCyclicPermutation(L, test);

//p.201: Discriminant 40, level Gamma(p2)
F := QuadraticField(40);
ZF := Integers(F);
p := Factorization(2*ZF)[1][1];
L := CuspResolutionIntersections(F, 1*ZF, p, F!1, F!0);
test := [-2,-3,-4,-3];
assert EqUpToCyclicPermutation(L, test);
return true;
