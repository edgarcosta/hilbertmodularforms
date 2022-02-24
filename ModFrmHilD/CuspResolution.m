
intrinsic OneAsLinearCombination(F :: FldQuad, a :: FldQuadElt, Ia :: RngQuadFracIdl,
				 b :: FldQuadElt, Ib :: RngQuadFracIdl) -> FldQuadElt, FldQuadElt
								     
{Compute lambda in Ia, mu in Ib such that lambda*a + mu*b = 1, assuming they exist}
    xa, ya := Explode(Basis(Ia));
    xb, yb := Explode(Basis(Ib));
    latticegens := [a*x: x in [xa,ya]] cat [b*x: x in [xb,yb]];
    M := ZeroMatrix(Integers(), 2, 4);
    for j := 1 to 4 do
	S := ElementToSequence(latticegens[j]);
	for i := 1 to 2 do M[i, j] := S[i]; end for;
    end for;
    target = Vector(Integers(), 2, [1,0]);
    sol, N := Solution(Transpose(M), target); //Runtime error if fails
    lambda := sol[1]*xa + sol[2]*ya;
    mu := sol[2]*xb + sol[2]*yb;

    assert lambda*a + mu*b eq 1;
    assert lambda in Ia;
    assert lambda in Ib;    
end intrinsic;

intrinsic CuspChangeMatrix(F :: FldQuad, b :: RngQuadFracIdl,
			   alpha :: FldQuadElt, beta :: FldQuadElt) -> AlgMatElt

{Given alpha, beta in F not both zero, compute g in SL2(F) such that
g(alpha:beta) = oo with the following property: if I = alpha*ZF +
beta*b^-1, then g has the shape [I^-1, I^-1*b^-1; I*b, I]}
    
    require alpha ne 0 or beta ne 0: "alpha or beta must be nonzero";
    ZF := Integers(F);
    I := alpha * ZF + beta * b^-1;
    lambda, mu := OneAsLinearCombination(F, alpha, I^-1, beta, I^-1*b^-1);
    g := Matrix(F, 2, 2, [lambda, mu, -beta, alpha]);
    assert Determinant(g) eq 1;
    return g;
end intrinsic;

intrinsic NormalizeCusp(F :: FldQuad, alpha :: FldQuadElt,
			beta :: FldQuadElt, n :: RngQuadIdl) -> FldQuadElt, FldQuadElt

{Given alpha, beta not both zero, compute another representation
(alpha', beta') of (alpha:beta) in P^1(F) such that alpha, beta are
integers and one of them is coprime to n}
    
    ZF := Integers(F);
    Cl, m := ClassGroup(F);
    primelift := ClassGroupPrimeRepresentatives(ZF, n);
    fac := [f[1] : f in Factorization(n)];
    
    for p in fac do
	n := Max(Valuation(alpha, p), Valuation(beta, p));
	pnclass := (p^n) @ m; //class of p^n in the ideal class group
	//We want to compute a generator of p^n * c, where c is coprime to n
	c := (pnclass^-1) @ primelift;
	gens := Generators(c * p^n);
	assert #gens eq 1;
	gen := gens[1];
	alpha := gen*alpha;
	beta := gen*beta;
    end for;
    //Now alpha, beta should be coprime to n
    assert IsCoprime(alpha*ZF, n);
    assert IsCoprime(beta*ZF, n);

    //Convert to integers
    denom := Gcd(alpha*ZF, beta*ZF);
    denom := Gcd(denom, ZF);
    denom := denom^-1; //denom is an integer ideal
    c := ((denom^-1) @ m) @ primelift;
    gens := Generators(c * denom);
    assert #gens eq 1;
    gen := gens[1];
    alpha := gen*alpha;
    beta := gen*beta;
    assert alpha in ZF;
    assert beta in ZF;

    //Simplify when possible: enumerate divisors of Gcd which are principal ideals
    g := Gcd(alpha*ZF, beta*ZF);
    prdivs := [p : p in Divisors(g) | IsPrincipal(p) and p ne 1*ZF];
    while prdivs ne [] do
	p := prdivs[1];
	c := Generators(p)[1];
	alpha := alpha/gen;
	beta := beta/gen;
	g := Gcd(alpha*ZF, beta*ZF);
	prdivs := [p : p in Divisors(g) | IsPrincipal(p) and p ne 1*ZF];
    end while;
    
    return alpha, beta;    
end intrinsic;
										
intrinsic CuspCRT(F :: FldQuad, a :: RngQuadFracIdl, n :: RngQuadIdl, y :: FldQuadElt)
	  -> FldQuadElt

{Assuming a and the denominator of y are coprime to n, compute x in a such that x=y mod n}
    require IsCoprime(a, n): "a and n must be coprime";
    ZF := Integers(F);
    denom := Gcd(y*ZF, 1*ZF)^-1;
    require IsCoprime(denom, n): "n and denominator of y must be coprime";
    
    a := Lcm(a, Integers(F)); //Now an integral ideal
    //Find a multiple of denominator of y which is 1 mod n
    d := CRT(denom, n, ZF!0, ZF!1);
    x := CRT(a, n, ZF!0, d*y);

    assert x in a;
    assert x-d*y in n;    
    return x;
end intrinsic;

intrinsic NormalizedCuspChangeMatrix(F :: FldQuad, b :: RngQuadFracIdl,
				     alpha :: FldQuadElt, beta :: FldQuadElt,
				     n :: RngQuadIdl) -> AlgMatElt

{Given a cusp (alpha:beta) that is normalized with respect to n
(cf. NormalizeCusp), compute g as in CuspChangeMatrix with the
additional property that the conjugation g*[v, m; 0, 1]*g^-1 is of the
form [1+xm, y(v-1)+zm; xm, y(v-1)+zm+1] modulo n, for some x,y,z in
ZF/n with y invertible}

    require IsNormalizedCusp(F, alpha, beta, n): "Cusp must be normalized (see CuspNormalize)";
    require IsCoprime(b, n): "b must be prime to the level n";
				
    g := CuspChangeMatrix(F, b, alpha, beta);
    if beta ne 0 then
	x := CuspCRT(F, I^-1*b^-1, n, alpha/beta);
	g := g * Matrix(F, 2, 2, [1, x, 0, 1]);
    end if;
    return g;
end intrinsic;
				     
intrinsic IsCoprime(a :: RngQuadFracIdl, b :: RngQuadFracIdl) -> Bool
{Decide if fractional ideals a and b are coprime}
    
    if a eq 0*a or b eq 0*b then return false;
    end if;
    a := Lcm(a, a^-1);
    b := Lcm(b, b^-1);
    return IsCoprime(a, b);
end intrinsic;       

intrinsic CuspResolutionM(F :: FldQuad, b :: RngQuadFracIdl, n :: RngQuadIdl,
			  alpha :: FldQuadElt, beta::FldQuadElt
			  : flag := -1) ->  RngQuadFracIdl
						
{Compute the module M in Van der Geer's notation as a fractional ideal in F.
See CuspResolutionIntersections for restrictions and definition of flags}
    ZF := Integers(F);
    a := alpha*ZF + beta*b^-1;
    if flag in [-1..2] then 
	return a^-2 * b^-1 * n;
	end if;
end intrinsic;

intrinsic CuspResolutionV(n :: RngQuadIdl : flag := -1) -> RngIntElt
{Return encoding for the congruence conditions defining V in Van der
Geer's notation. See CuspResolutionIntersections for definition of flags.

Result semantics:
0 means V consists of squares of units
1 means V consists of squares of (units which are 1 mod n)
2 means V consists of (squares of units) which are 1 mod n}
    requirerange flag, -1, 2;
    case flag:
    when -1:
	return 1;
    when 0:
	return 0;
    when 1:
	return 1;
    when 2:
	return 2;
    end case;
end intrinsic;

intrinsic CuspResolutionMinimalSequence(F :: FldQuad, M :: RngQuadFracIdl) -> SeqEnum[RngIntElt]
{Compute the periodic part of the HJ continued fraction, as in Van der Geer p.38}
    require M ne 0*M: "Module M must not be zero";
    a, b := Explode(Basis(M));
    head, periodic := HJContinuedFraction(F ! (a/b));
    return periodic;
end intrinsic;

intrinsic CuspResolutionMinimalUnit(F :: FldQuad, per :: SeqEnum[RngIntElt]) -> FldQuadElt
{Compute a generator of U_M+ in Van der Geer's notation}
    w := HJCyclicProductOfReconstructions(F, per);
    //Check that we indeed have a totally positive unit
    ZF := Integers(F);
    assert w in ZF;
    assert IsUnit(ZF!w) and IsTotallyPositive(ZF!w);
    return ZF!w;
end intrinsic;

//This very naive algorithm is still linear in size of final output
intrinsic UnitMultiplicativeOrderMod(ZF :: RngQuad, p :: RngQuadIdl, eps :: RngQuadElt) -> RngIntElt
{Compute the multiplicative order of a the unit eps modulo the ideal p}
    require p ne 0*p: "Ideal p must not be zero";
    require IsUnit(eps): "eps must be a unit";
    			 
    Q := quo<ZF|p>;
    n := 1;
    u := eps;
    while Q!1 ne Q!u do
        n := n+1; u := eps*u;
    end while;
    return n;
end intrinsic;

intrinsic UnitIsPm1Mod(ZF :: RngQuad, p :: RngQuadIdl, eps :: RngQuadElt) -> Bool
{Decide whether eps is +-1 mod p}
    require p ne 0*p: "Ideal p must not be zero";
    require IsUnit(eps): "eps must be a unit";

    Q := quo<ZF|p>;
    return (Q!1 eq Q!eps or Q!(-1) eq Q!eps);
end intrinsic;

intrinsic RepeatSequence(l :: SeqEnum, n :: RngIntElt) -> SeqEnum
{Output l repeated n times}
    return &cat[l : x in [1..n]];
end intrinsic;

intrinsic CuspResolutionIntersections(F :: FldQuad, b :: RngQuadFracIdl, n :: RngQuadIdl,
				      alpha :: FldQuadElt, beta::FldQuadElt
				      : flag := -1) -> SeqEnum[RngIntElt]
							      
{Compute the cyclic sequence of self-intersection numbers for the
cycle of P1's appearing in the appearing in the resolution of the cusp
(alpha:beta) in P^1(F) for the modular group SL(ZF+b) and congruence
subgroup of level n (prime to b).
                                                                                                   
Accepted flags are:
-1 for full level Gamma(n);
0  for Gamma_0(n);
1  for Gamma_1(n);
2  for Ker(Gamma(1) -> PSL(ZF/n)}

    require IsCoprime(n, b):
	  "Ideals b (defining the full modular group) and n (defining the level) must be coprime";
    require alpha ne 0 or beta ne 0:
	  "Cusp (alpha:beta) in P^1 cannot have both coordinates zero";
    requirerange flag, -1, 2;

    ZF := Integers(F);
    M := CuspResolutionM(F, b, n, alpha, beta: flag:=flag);
    V := CuspResolutionV(n: flag:=flag);
    periodic := CuspResolutionMinimalSequence(F, M);
    w := CuspResolutionMinimalUnit(F, periodic);
    issqr, x := IsSquare(w);

    m := UnitMultiplicativeOrderMod(ZF, n, w);
        
    if issqr then
	case V:
	when 0:
	    m := 1;
	when 1:
	    m := m;
	when 2:
	    if UnitIsPm1Mod(ZF, n, x^m) then m := m;
	    else m := 2*m;
	    end if;
	end case;
    else
	case V:
	when 0:
	    m := 2;
	when 1:
	    if IsEven(m) and UnitIsPm1Mod(ZF, n, w^(m div 2)) then m := m;
	    else m := 2*m;
	    end if;
	when 2:
	    m := Lcm(2, m);
	end case;
    end if;
    L := RepeatSequence(periodic, m);
    L := [-b: b in L];
    if #L eq 1 then L := [L[1]+2]; end if;
    return L;
end intrinsic;
