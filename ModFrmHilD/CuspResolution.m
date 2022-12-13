
intrinsic OneAsLinearCombination(F :: FldQuad, a :: FldQuadElt, Ia :: RngQuadFracIdl,
				 b :: FldQuadElt, Ib :: RngQuadFracIdl) -> FldQuadElt, FldQuadElt
								     
{Compute lambda in Ia, mu in Ib such that lambda*a + mu*b = 1, assuming they exist}
    xa, ya := Explode(Basis(Ia));
    xb, yb := Explode(Basis(Ib));
    latticegens := [a*x: x in [xa,ya]] cat [b*x: x in [xb,yb]];
    
    //Get a common denominator D for all coefficients
    D := 1;
    for j:=1 to 4 do
	S := ElementToSequence(latticegens[j]);
	D := Lcm(D, Lcm([Denominator(x): x in S]));
    end for;

    //Construct linear algebra problem over ZZ
    M := ZeroMatrix(Integers(), 2, 4);
    for j := 1 to 4 do
	S := ElementToSequence(latticegens[j]);
	for i := 1 to 2 do M[i, j] := D*S[i]; end for;
    end for;
    target := Vector(Integers(), 2, [D,0]);
    sol, N := Solution(Transpose(M), target); //Runtime error if fails

    //Set result and check
    lambda := sol[1]*xa + sol[2]*ya;
    mu := sol[3]*xb + sol[4]*yb;

    assert lambda*a + mu*b eq 1;
    assert lambda in Ia;
    assert mu in Ib;
    return lambda, mu;
end intrinsic;

intrinsic CuspChangeMatrix(F :: FldQuad, b :: RngQuadFracIdl,
			   alpha :: FldQuadElt, beta :: FldQuadElt) -> AlgMatElt

{Given alpha, beta in F not both zero, compute g in SL2(F) such that
g(alpha:beta) = oo with the following property: if I = alpha*ZF +
beta*b^-1, then g has the shape [I^-1, I^-1*b^-1; -beta, alpha]}

    require alpha ne 0 or beta ne 0: "alpha or beta must be nonzero";
    ZF := Integers(F);
    I := alpha * ZF + beta * b^-1;
    lambda, mu := OneAsLinearCombination(F, alpha, I^-1, beta, I^-1*b^-1);
    g := Matrix(F, 2, 2, [lambda, mu, -beta, alpha]);
    assert Determinant(g) eq 1;
    return g;
end intrinsic;

intrinsic IdealClassPrimeRepresentative(m :: Map, p :: RngQuadFracIdl) -> RngQuadIdl
									      
{Given a map m computed via ClassGroupPrimeRepresentatives, find an
element in the image of m that belongs to the class of p. This solves
a Magma issue that reduction map from ClassGroup and lift map from
ClassGroupPrimeRepresentatives do not seem to be compatible}

    pinv := p^-1;
    for cl in Domain(m) do
	lift := cl@m;
	if IsPrincipal(pinv * lift) then
	    assert IsPrincipal(lift * p^-1);
	    return lift;
	end if;
    end for;
end intrinsic;
			

intrinsic NormalizeCusp(F :: FldQuad, alpha :: FldQuadElt,
			beta :: FldQuadElt, n :: RngQuadIdl) -> FldQuadElt, FldQuadElt

{Given alpha, beta not both zero, compute another representation
(alpha', beta') of (alpha:beta) in P^1(F) such that alpha, beta are
integers, and alpha, beta, n are globally coprime}
    
    ZF := Integers(F);
    primelift := ClassGroupPrimeRepresentatives(ZF, n);
    fac := [f[1] : f in Factorization(n)];

	//Enforce coprimality condition
    for p in fac do
	v := Min(Valuation(alpha, p), Valuation(beta, p));
	c := IdealClassPrimeRepresentative(primelift, p^v);
	t, gen := IsPrincipal(c*p^(-v));
	assert t;
	alpha := gen*alpha;
	beta := gen*beta;
    end for;	
    assert IsCoprimeFracIdl(alpha*ZF, Gcd(beta*ZF, n));

    //Convert to integers
    denom := Gcd(alpha*ZF, beta*ZF);
    denom := Gcd(denom, 1*ZF)^-1; //denom is an integer ideal
    //denom;
    c := IdealClassPrimeRepresentative(primelift, denom^-1);
    t, gen := IsPrincipal(c * denom);
    assert t;
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

intrinsic IsNormalizedCusp(F :: FldQuad, alpha :: FldQuadElt, beta :: FldQuadElt,
			   n :: RngQuadIdl) -> Bool
{True iff alpha, beta are both integral alpha, beta, n are coprime}
    ZF := Integers(F);
    ints := alpha in 1*ZF and beta in 1*ZF;
    coprime := IsCoprimeFracIdl(alpha*ZF, Gcd(beta*ZF, n));
    return ints and coprime;
end intrinsic;

intrinsic IsNormalizedCuspChangeMatrix(F::FldQuad, b :: RngQuadFracIdl,
				       n::RngQuadIdl, g::AlgMatElt) -> Bool
{Decide whether g is of the form [lambda, mu; -beta, alpha] where:
- (alpha, beta) is a normalized cusp;
- lambda is in I^-1 and mu is in I^-1*b^-1, where I=alpha*ZF + beta*b^-1;
- g has determinant 1.}

    alpha := g[2,2];
    beta := -g[2,1];
    lambda := g[1,1];
    mu := g[1,2];
    if not IsNormalizedCusp(F, alpha, beta, n) then return false; end if;
    ZF := Integers(F);
    I := alpha*ZF + beta*b^-1;
    return (lambda in I^-1) and (mu in I^-1*b^-1) and (Determinant(g) eq 1);    
end intrinsic;
			
		     
intrinsic IsCoprimeFracIdl(a :: RngOrdFracIdl, b :: RngOrdFracIdl) -> Bool
{Decide if fractional ideals a and b are coprime}
    if a eq 0*a or b eq 0*b then return false;
    end if;
    a := Lcm(a, a^-1);
    b := Lcm(b, b^-1);
    a, da := IntegralSplit(a); assert da eq 1 or da eq -1;
    b, db := IntegralSplit(b); assert db eq 1 or db eq -1;
    return IsCoprime(a, b);
end intrinsic;       


intrinsic CuspResolutionCongruences(F::FldQuad, b :: RngQuadFracIdl,
				    n::RngQuadIdl, g::AlgMatElt, p::RngQuadIdl
				    : GammaType := "Gamma0")
	  -> SeqEnum[RngIntElt], RngQuadElt
				     
{Given a cusp change matrix g computed from a normalized cusp for
level n, and given a prime divisor p of n, compute a suitable change
of the form [1,x;0,1] such that g^-1 [v,m;0,v^-1] g gives congruence
conditions of the form G(M,V) on m and v. Output: minimal p-adic
valuations of v-1, v^2-1, m, x-x0, as well as a suitable x0 (always an
integer divided by 2*alpha*beta, if alpha*beta is not zero, otherwise
just an integer divided by beta)}

    require IsCoprimeFracIdl(p, b): "p and b must be coprime";
    
    require IsNormalizedCuspChangeMatrix(F, b, n, g): "g must be a
    normalized cusp change matrix";

    //Get p-adic valuations of beta, n
    lambda := g[1,1];
    mu := g[1,2];
    beta := -g[2,1];
    alpha := g[2,2];
    
    e := Valuation(n, p);
    f := Valuation(beta, p); //Infinity if beta=0
    f := Min(e, f);
    ZF := Integers(F);
    I := alpha * ZF + beta * b^-1;

    if not IsNormalizedCusp(F, alpha, beta, n) then
	error "Not a cusp change matrix attached to a normalized cusp";
    end if;
    assert IsCoprimeFracIdl(p, I); //Enforced by normalized cusp
    N := I^(-2)*b^(-1);
    
    if GammaType eq "Gamma0" or GammaType eq "Gamma01" then
		if f eq 0 then
			if alpha eq 0 then x0 := lambda;
			else x0 := 2*lambda*alpha;
			end if;
			exps := [0, 0, e, e];
		elif 2*f lt e then
			if alpha eq 0 then x0 := lambda;
			else x0 := 2*lambda*alpha;
			end if;
			exps := [0, f, e-2*f, e-f];
		else
			exps := [0, e-f, 0, 0];
			x0 := ZF!0;
		end if;
		if GammaType eq "Gamma01" then
			exps[2] := e;
		end if;
	
    elif GammaType eq "Gamma1" or GammaType eq "Gamma11" then
		exps := [e, e, e-f, 0];
		x0 := (1-2*beta*mu);

	elif GammaType eq "GammaP" then
		exps := [0, e, e, 0];
		x0 := ZF!0;
	
    elif GammaType eq "Gamma" then
		exps := [e, e, e, 0];
		x0 := ZF!0;
    else error "GammaType not recognized";
    end if;

	return exps, ZF!x0;
end intrinsic;
		    

intrinsic CuspResolutionMV(F::FldQuad, b::RngQuadFracIdl, n::RngQuadIdl,
			   alpha::FldQuadElt, beta::FldQuadElt: GammaType := "Gamma0")
	  -> SeqEnum[RngQuadIdl], AlgMatElt
					  
{Given a normalized cusp (alpha:beta), compute ideals M, W, W2 and a
change-of-cusp matrix g sending (alpha:beta) to infinity such that:

- g is of the form [I^-1, (Ib)^-1; Ib, I] where I = alpha*ZF +
  beta*b^-1;

- g^-1 [v,m;0,v^-1] lies in the given level subgroup precisely when
  m,v satisfy conditions of the form G(M,V).

V is encoded as congruence conditions on v-1 and v^2-1, given by
ideals W, W2 respectively.}
    
    require IsNormalizedCusp(F, alpha, beta, n): "Cusp (alpha:beta) must be normalized";

    //print "Computing cusp change matrix...";
    g := CuspChangeMatrix(F, b, alpha, beta);
    plist := [f[1]: f in Factorization(n)];

    ZF := Integers(F);
    I := alpha*ZF + beta*b^-1;
    M0 := I^-2 * b^-1;

    M := M0;
    W := 1*ZF; //Congruence conditions on v-1
    W2 := 1*ZF; //Congruence conditions on v^2-1
    X := 1*ZF; //Congruence conditions on x-x0;
    x := ZF!0;
    
    for p in plist do
	//print "Computing congruence conditions...";
	L, x0 := CuspResolutionCongruences(F, b, n, g, p: GammaType:=GammaType);
	ev, ev2, em, ex := Explode(L);
	//print "Congruences of cusp coordinates:", ev, ev2, em, ex;
	M *:= p^em;
	W *:= p^ev;
	W2 *:= p^ev2;
	//Update x0 by solving a Chinese remaindering problem in ZF
	x := CRT(X, p^ex, x, x0);
	X *:= p^ex;
    end for;
    if alpha*beta ne 0 and x ne 0 then
	//Clear out any denominator coprime to n
	x := x/(2*alpha*beta);
	qlist := [f[1]: f in Factorization(2*alpha*beta*ZF)];
	for q in qlist do
	    v := Valuation(x, q);
	    if v lt 0 and Valuation(n, q) eq 0 then
		x *:= CRT(n, q^(-v), ZF!1, ZF!0);
	    end if;
	end for;
    end if;
    g := Matrix(F, 2, 2, [F!1, x, 0, F!1]) * g;

    return [M, W, W2], g;
end intrinsic;
    

intrinsic CuspResolutionMinimalSequence(F :: FldQuad, M :: RngQuadFracIdl) -> SeqEnum[RngIntElt]
{Compute the periodic part of the HJ continued fraction, as in Van der Geer p.38}
    require M ne 0*M: "Module M must not be zero";

    a,b := OrientedBasis(M);
    
    head, periodic := HJContinuedFraction(F ! (a/b));
    return periodic;
end intrinsic;

intrinsic OrientedBasis(M :: RngQuadFracIdl) -> Any
{}
    //print Basis(M);
    a, b := Explode(Basis(M));
    F := NumberField(Order(M));
    fa := F ! a;
    fb := F ! b;

    _, ori := Explode(Eltseq(fa * Conjugate(fb) - fb * Conjugate(fa)));
    if ori lt 0 then
        return b, a;
    else
        return a, b;
    end if;
    error "Basis returned for module M invalid.";
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

intrinsic RepeatSequence(l :: SeqEnum, n :: RngIntElt) -> SeqEnum
{Output l repeated n times}
    return &cat[l : x in [1..n]];
end intrinsic;


intrinsic CuspResolutionIntersections(G::StupidCongruenceSubgroup, p::Pt) -> SeqEnum
{}
    K := Field(G);
    N := Level(G);
    x, y := Explode(Coordinates(p));
    x, y := NormalizeCusp(K, x, y, N);
    return CuspResolutionIntersections(K, Component(G), N, x, y : GammaType:=GammaType(G));
end intrinsic;

// this is the top-level function
intrinsic CuspResolutionIntersections(F :: FldQuad, b :: RngQuadFracIdl, n :: RngQuadIdl,
				      alpha :: FldQuadElt, beta::FldQuadElt
				      : GammaType := "Gamma0") -> SeqEnum[RngIntElt]
							      
{Compute the cyclic sequence of self-intersection numbers for the
cycle of P1's appearing in the appearing in the resolution of the cusp
(alpha:beta) in P^1(F) for the modular group SL(ZF+b) and congruence
subgroup of level n (prime to b).
                                                                                                   
Accepted values for the parameter GammaType are: "Gamma0" (default);
"Gamma1"; "Gamma" (full level); "GammaP" for
Ker(Gamma(1)->PSL(ZF/n)).}

    require IsNormalizedCusp(F, alpha, beta, n): "Cusp (alpha,beta) must be normalized";

    ZF := Integers(F);
    L, g := CuspResolutionMV(F, b, n, alpha, beta: GammaType := GammaType);
    M, W, W2 := Explode(L);
    
    //print "Ideals M, W, W2:", M, W, W2;

    //Compute minimal totally positive unit stabilizing M.
    periodic := CuspResolutionMinimalSequence(F, M);
    w := CuspResolutionMinimalUnit(F, periodic);
    
    issqr, t := IsSquare(w);
    //print w; print "IsSquare?", issqr;
    n := 1;
    if issqr then
	//V is gen'd by w^n, where n minimal s.t. w^n-1 = 0 mod W2 and t^n +/- 1 = 0 mod W
	while not (w^n-1 in W2 and (t^n-1 in W or t^n + 1 in W)) do n +:= 1; end while;
    else
	//V is gen'd by w^(2n), where n minimal s.t. w^(2n)-1 = 0 mod W2 and w^n +/- 1 = 0 mod W
	while not (w^(2*n)-1 in W2 and (w^n-1 in W or w^n + 1 in W)) do n +:= 1; end while;
	n := 2*n;
    end if;

    L := [-b: b in periodic];
    if #L eq 1 and n eq 1 then L := [L[1]+2]; end if;
    return L, n;
end intrinsic;

intrinsic GeneratorsOfGMV(F::FldQuad, b::RngQuadIdl, alpha::FldQuadElt,
			  beta::FldQuadElt, S::SeqEnum[RngQuadFracIdl]) ->
	  SeqEnum[AlgMatElt]

{Return three matrices that generate G(M,V) as a group}

    //Get generator of V_M+
    M, W, W2 := Explode(S);
    periodic := CuspResolutionMinimalSequence(F, M);
    w := CuspResolutionMinimalUnit(F, periodic);
    assert IsUnit(w);
    issqr, t := IsSquare(w);
    //print w; print "IsSquare?", issqr;
    n := 1;
    //print w, W2, W, t, Norm(W), Norm(W2);
    if issqr then
	//V is gen'd by w^n, where n minimal s.t. w^n-1 = 0 mod W2 and t^n +/- 1 = 0 mod W
	while not (w^n-1 in W2 and (t^n-1 in W or t^n + 1 in W)) do
	    //print n;
	    n +:= 1; end while;
	if t^n-1 in W then u := t^n; else u := -t^n; end if;
    else
	//V is gen'd by w^(2n), where n minimal s.t. w^(2n)-1 = 0 mod W2 and w^n +/- 1 = 0 mod W
	while not (w^(2*n)-1 in W2 and (w^n-1 in W or w^n + 1 in W)) do n +:= 1; end while;
	if w^n-1 in W then u := w^n; else u := -w^n; end if;
    end if;
    U1 := Matrix(F, 2, 2, [u, F!0, F!0, u^-1]);

    x, y := Explode(Basis(M));
    U2 := Matrix(F, 2, 2, [F!1, x, F!0, F!1]);
    U3 := Matrix(F, 2, 2, [F!1, y, F!0, F!1]);
    return [U1, U2, U3];    
end intrinsic;

intrinsic TestCuspChangeMatrix(F::FldQuad, b::RngQuadIdl, n::RngQuadIdl,
			       alpha::FldQuadElt, beta::FldQuadElt: GammaType:="Gamma0")
{Check that conjugating elements of G(M,V) by g indeed gives matrices
in the correct level subgroup}

    S, g := CuspResolutionMV(F, b, n, alpha, beta: GammaType:=GammaType);
    Ulist := GeneratorsOfGMV(F, b, alpha, beta, S);
    for U in Ulist do
	V := g^-1 * U * g;
	if GammaType eq "Gamma0" then
	    valid := V[2,1] in n;
	elif GammaType eq "Gamma1" then
	    valid := V[2,1] in n and V[1,1]-1 in n;
	elif GammaType eq "Gamma" then
	    valid := V[2,1] in n and V[1,1]-1 in n and V[1,2] in n;
	elif GammaType eq "GammaP" then
	    valid := V[2,1] in n and V[1,1]-V[2,2] in n and V[1,2] in n;
	else
	    error "GammaType not recognized";
	end if;
	if not valid then
	    ZF := Integers(F);
	    plist := [f[1]: f in Factorization(n)];
	    for p in plist do
		print "Debug info:";
		print p;
		print Valuation(U[1,1]-U[2,2], p);
		print Valuation(V[2,1], p);
		print Valuation(V[1,1]-1, p);
	    end for;
	    error "Invalid matrices", U, V, g; end if;
    end for;
end intrinsic;

