es := AssociativeArray();
ds := [5,13,17,29,37,41,53,61,73,89,97,101,109,113,137,149,157,173,181,193,
       197,229,233,241,257,269,277,281,293,313,317,337,349,353,373,389,397,
       401,409,421,433,449,457,461];
e_vals := [14,15,16,28,29,30,40,41,43,52,53,60,61,60,68,78,77,86,85,103,94,
           97,114,133,116,112,133,142,120,161,126,185,143,148,175,162,153,194,
           225,175,225,216,247,174];

assert #e_vals eq #ds;
for i in [1..#ds] do
    es[ds[i]] := e_vals[i];
end for;

function PrimeDiscriminant(D,q)
    assert D mod q eq 0;
    assert IsFundamentalDiscriminant(D);
    sign := (q mod 4 eq 1) select 1 else -1;
    if (q eq 2) then
	sign := &*[(-1) : p in PrimeDivisors(D) | p mod 4 eq 3];
    end if;
    return sign*q^Valuation(D,q);
end function;

// For K2, vdG only lists the value after blowing down succesively 
// HZ execptional curves, we need to know how many there are to compare.
function getHZExceptionalNum(Gamma)
    assert Norm(Level(Gamma)) eq 1;
    A := Norm(Component(Gamma));
    D := Discriminant(Integers(Field(Gamma)));
    qs := PrimeDivisors(D);
    Dqs := [PrimeDiscriminant(D,q) : q in qs];
    s := 2*&*[1 + KroneckerSymbol(Dq,A) : Dq in Dqs];
    s +:= &*[1 + KroneckerSymbol(Dq, 2*A) : Dq in Dqs];
    s +:= &*[1 + KroneckerSymbol(Dq, 3*A) : Dq in Dqs] div 2;
    s +:= (1 - KroneckerSymbol(D,3)^2)* 
	  &*[1 + KroneckerSymbol(Dq,9*A) : Dq in Dqs];
    if D eq 105 then
	s +:= 2;
    end if;
    return s;
end function;

printf "Testing Euler number of level 1, discriminant... D=";
for d in ds do
    printf "%o ", d;
    F := QuadraticField(d);
    G := Gamma0(F, 1*Integers(F));
    assert EulerNumber(G) eq es[d];
end for;

ds := [d : d in [2..500] | IsFundamentalDiscriminant(d)];
ds := [d : d in ds | d notin [8,12]];
DN_bound := 500;

printf "Testing integrality of genus for some random (disc;level;comp)...";

for _ in [1..10] do
    d := Random(ds);
    F := QuadraticField(d);
    ZF := Integers(F);
    N := Random(IdealsUpTo(Floor(DN_bound/d),F : CoprimeTo := 3*d*ZF));
    cg, cg_map := NarrowClassGroup(F);
    b := Random(cg);
    B := cg_map(b);
    printf "(%o;%o;%o),", d,IdealOneLine(N),IdealOneLine(B);
    a := CoprimeNarrowRepresentative(B,N);
    assert IsTotallyPositive(a);
    assert a*B + N eq 1*Order(N);
    B := a*B;    
    G_SL := CongruenceSubgroup("SL", "Gamma0", F, N, B);
    chi := ArithmeticGenus(G_SL);
    assert IsIntegral(chi);
    /*
    G_GL := CongruenceSubgroup("GL+", "Gamma0", F, N, B);
    chi := ArithmeticGenus(G_GL);
    assert IsIntegral(chi);
   */
end for;

// Print newline.
print "";
