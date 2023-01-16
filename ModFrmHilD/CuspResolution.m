
/* ------------------------------------------------------------------------- */
/* Helper functions for ideals */

intrinsic OneAsLinearCombination(a :: FldNumElt, Ia :: RngOrdFracIdl,
                                 b :: FldNumElt, Ib :: RngOrdFracIdl)
          -> FldNumElt, FldNumElt
{Compute lambda in Ia, mu in Ib such that lambda*a + mu*b = 1, assuming they exist}

    F := NumberField(Order(Ia));
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


intrinsic IdealFromFractionalIdeal(I :: RngOrdFracIdl) -> RngOrdIdl
{Return I as an integral ideal}
    ZF := Order(I);
    a, b := Explode(Basis(I));
    return a*ZF + b*ZF;
end intrinsic;

intrinsic IdealClassPrimeRepresentative(m :: Map, p :: RngOrdFracIdl) -> RngOrdIdl

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


intrinsic IsUnitModIdeal(n::RngOrdIdl, x::FldElt) -> Bool
{True iff x is integral, prime to n and there exists a unit u such that x=u mod n}
    ZF := Order(n);
    F := NumberField(ZF);
    if n eq 1*ZF then return true; end if;
    w := FundamentalUnit(F);
    if not x in ZF then return false; end if;
    Q := quo<ZF|n>;
    if not IsUnit(Q!x) then return false; end if;
    U, m := UnitGroup(Q);
    gens := [(Q!(-ZF!1))@@m, (Q!w)@@m];
    S := sub<U|gens>;
    return (Q!x)@@m in S;
end intrinsic;

/* ------------------------------------------------------------------------- */
/* Normalize cusps, change of cusp */

intrinsic NormalizeCusp(b :: RngOrdFracIdl, n :: RngOrdIdl, alpha :: FldNumElt,
                        beta :: FldNumElt) -> FldNumElt, FldNumElt
{Given alpha, beta not both zero, compute another representation
(alpha', beta') of (alpha:beta) in P^1(F) such that alpha*ZF, beta*b^(-1) are
integral ideals, and alpha, beta, n are globally coprime}

    require IsCoprimeFracIdl(n, b): "Ideals n and b (level and connected component) must be coprime";

    ZF := Order(b);
    F := NumberField(ZF);
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

    //Convert to integers
    denom := Gcd(alpha*ZF, beta*b^(-1));
    denom := Gcd(denom, 1*ZF)^-1; //denom is an integer ideal
    //denom;
    c := IdealClassPrimeRepresentative(primelift, denom^-1);
    t, gen := IsPrincipal(c * denom);
    assert t;
    alpha := gen*alpha;
    beta := gen*beta;
    assert alpha in ZF;
    assert beta in b;

    //Simplify when possible: enumerate divisors of Gcd which are principal ideals
    g := IdealFromFractionalIdeal(Gcd(alpha*ZF, beta*b^(-1)));
    prdivs := [p : p in Divisors(g) | IsPrincipal(p) and p ne 1*ZF];
    while prdivs ne [] do
        p := prdivs[1];
        _, gen := IsPrincipal(p);
        alpha := alpha/gen;
        beta := beta/gen;
        g := IdealFromFractionalIdeal(Gcd(alpha*ZF, beta*b^(-1)));
        prdivs := [p : p in Divisors(g) | IsPrincipal(p) and p ne 1*ZF];
    end while;

    assert IsNormalizedCusp(b, n, alpha, beta);
    return alpha, beta;
end intrinsic;


intrinsic IsNormalizedCusp(b :: RngOrdFracIdl, n :: RngOrdIdl,
                           alpha :: FldNumElt, beta :: FldNumElt) -> Bool
{True iff alpha*ZF, beta*b^(-1) are both integral ideals and alpha, beta, n are coprime}
    ZF := Order(b);
    ints := alpha in 1*ZF and beta in b;
    coprime := IsCoprimeFracIdl(alpha*ZF, Gcd(beta*ZF, n));
    return ints and coprime;
end intrinsic;

intrinsic CuspChangeMatrix(b :: RngOrdFracIdl,
                           alpha :: FldNumElt, beta :: FldNumElt) -> AlgMatElt

{Given alpha, beta in F not both zero, compute g in SL2(F) such that
g(alpha:beta) = oo with the following property: if I = alpha*ZF +
beta*b^-1, then g has the shape [I^-1, I^-1*b^-1; -beta, alpha]}

    require alpha ne 0 or beta ne 0: "alpha or beta must be nonzero";
    ZF := Order(b);
    F := NumberField(ZF);
    I := alpha * ZF + beta * b^-1;
    lambda, mu := OneAsLinearCombination(alpha, I^-1, beta, I^-1*b^-1);
    g := Matrix(F, 2, 2, [lambda, mu, -beta, alpha]);
    assert Determinant(g) eq 1;
    return g;
end intrinsic;

intrinsic IsNormalizedCuspChangeMatrix(b :: RngOrdFracIdl,
                                       n::RngOrdIdl, g::AlgMatElt) -> Bool
{Decide whether g is of the form [lambda, mu; -beta, alpha] where:
- (alpha, beta) is a normalized cusp;
- lambda is in I^-1 and mu is in I^-1*b^-1, where I=alpha*ZF + beta*b^-1;
- g has determinant 1.}

    alpha := g[2,2];
    beta := -g[2,1];
    lambda := g[1,1];
    mu := g[1,2];
    if not IsNormalizedCusp(b, n, alpha, beta) then return false; end if;
    ZF := Order(b);
    I := alpha*ZF + beta*b^-1;
    return (lambda in I^-1) and (mu in I^-1*b^-1) and (Determinant(g) eq 1);
end intrinsic;

/* ------------------------------------------------------------------------- */
/* Computing G(M,V) and cusp resolution */

intrinsic CuspResolutionCongruences(b :: RngOrdFracIdl,
                                    n::RngOrdIdl, g::AlgMatElt, p::RngOrdIdl
                                    : GammaType := "Gamma0", GroupType := "GL2+")
          -> SeqEnum[RngIntElt], FldNumElt

{Given a cusp change matrix g computed from a normalized cusp for
level n, and given a prime divisor p of n, compute a suitable change
of the form [1,x;0,1] such that g^-1 [v,m;0,1] g gives congruence
conditions of the form G(M,V) on m and v. Output: minimal p-adic
valuations of v-1, v^2-1, m, x-x0, as well as a suitable x0 (always an
integer divided by 2*alpha*beta, if alpha*beta is not zero, otherwise
just an integer divided by beta)}

    require IsCoprimeFracIdl(p, b): "p and b must be coprime";
    require IsNormalizedCuspChangeMatrix(b, n, g): "g must be a
    normalized cusp change matrix";

    ZF := Order(b);
    F := NumberField(ZF);
    //Get p-adic valuations of beta, n
    lambda := g[1,1];
    mu := g[1,2];
    beta := -g[2,1];
    alpha := g[2,2];

    e := Valuation(n, p);
    f := Valuation(beta, p); //Infinity if beta=0
    f := Min(e, f);
    I := alpha * ZF + beta * b^-1;

    assert IsNormalizedCusp(b, n, alpha, beta);
    assert IsCoprimeFracIdl(p, I); //Enforced by normalized cusp
    N := I^(-2)*b^(-1);
    x0 := ZF!0;

    //Set additional valuation for CRT on x
    if alpha*beta ne 0 then
        add := Valuation(2*alpha*beta, p);
    elif beta ne 0 then
        add := Valuation(beta, p);
    else
        add := 0;
    end if;

    //Set x if necessary; we always have beta ne 0 in these cases
    if GammaType eq "Gamma0" and 2*f lt e then
        if alpha ne 0 then
            x0 := ZF!(2*lambda*alpha);
        else
            x0 := ZF!lambda;
        end if;
    elif GammaType eq "Gamma1" and f lt e then
        if alpha ne 0 then
            x0 := ZF!(2*lambda*alpha);
        else
            x0 := ZF!lambda;
        end if;
    end if;

    if GroupType eq "GL2+" then
        if GammaType eq "Gamma0" then
            if 2*f lt e then
                exps := [f, f, e-2*f, e-f+add];
            else
                exps := [e-f, e-f, 0, add];
            end if;
        elif GammaType eq "Gamma1" then
            if f lt e then
                exps := [f, f, e-f, e-f+add];
            else //f=e
                exps := [e, e, 0, add];
            end if;
        elif GammaType eq "Gamma" then
            exps := [e, e, e, add];
        else
            error "GammaType not recognized:", GammaType;
        end if;
    elif GroupType eq "SL2" then
        //[JK] This is taken from the previous code; todo: write proof in paper
        if GammaType eq "Gamma0" then
            if 2*f lt e then
                exps := [0, f, e-2*f, e-f+add];
            else
                exps := [0, e-f, 0, add];
            end if;
        elif GammaType eq "Gamma1" then
            if f lt e then
                exps := [e, e, e-f, e-f+add];
            else //f=e
                exps := [e, e, 0, add];
            end if;
        elif GammaType eq "GammaP" then
            exps := [0, e, e, add];
        elif GammaType eq "Gamma" then
            exps := [e, e, e, add];
        else
            error "GammaType not recognized:", GammaType;
        end if;
    else
        error "GroupType not recognized:", GroupType;
    end if;
    return exps, x0;
end intrinsic;

intrinsic CuspResolutionMV(b::RngOrdFracIdl, n::RngOrdIdl,
                              alpha::FldNumElt, beta::FldNumElt:
                              GammaType := "Gamma0",
                              GroupType := "GL2+")
          -> RngFracIdl, RngOrdElt, AlgMatElt
{Given a normalized cusp (alpha:beta), compute M, V and a change-of-cusp matrix
g sending (alpha:beta) to infinity such that g^-1 [v,m;0,1] lies in the given
level subgroup (as a transformation, i.e. up to a scalar matrix) precisely when
m,v satisfy conditions of the form G(M,V). Here V is encoded as a totally
positive unit that generates it.}

    require IsNormalizedCusp(b, n, alpha, beta): "Cusp (alpha:beta) must be normalized";

    g := CuspChangeMatrix(b, alpha, beta);
    assert IsNormalizedCuspChangeMatrix(b, n, g);
    plist := [f[1]: f in Factorization(n)];

    ZF := Order(b);
    F := NumberField(ZF);
    I := alpha*ZF + beta*b^-1; //Integral, coprime to n.
    M0 := I^-2 * b^-1;

    M := M0;
    W := 1*ZF; //Congruence conditions on v-1
    W2 := 1*ZF; //Congruence conditions on v^2-1
    X := 1*ZF; //Congruence conditions on x-x0;
    x := ZF!0;

    for p in plist do
        //Get congruences mod powers of p
        L, x0 := CuspResolutionCongruences(b, n, g, p:
                                           GammaType:=GammaType, GroupType:=GroupType);
        ev, ev2, em, ex := Explode(L);
        M *:= p^em;
        W *:= p^ev;
        W2 *:= p^ev2;
        //Update x0 by solving a Chinese remaindering problem in ZF
        x := CRT(X, p^ex, x, x0);
        X *:= p^ex;
    end for;
    if alpha*beta ne 0 then
        x := x/(2*alpha*beta);
    elif beta ne 0 then
        x := x/beta;
    end if;

    //Make x belong to I^(-2)b^(-1) except for factors of n
    if not x in I^(-2)*b^(-1) then
        idl := 1*ZF;
        for fac in Factorization(x*ZF) do
            p := fac[1];
            if not n subset p then
                val1 := Valuation(x*ZF, p);
                val2 := Valuation(I^(-2)*b^(-1), p);
                if val1 lt val2 then
                    idl *:= p^(val2 - val1);
                end if;
            end if;
        end for;
        //Find element in idl, congruent to 1 mod n
        scal := CRT(n, idl, ZF!1, ZF!0);
        assert scal in ZF;
        assert scal in idl;
        assert scal-1 in n;
        x *:= scal;
    end if;

    V := CuspResolutionV(W, W2: GroupType:=GroupType);
    return M, V, Matrix(F, [[1,x],[0,1]])*g;
end intrinsic;

intrinsic CuspResolutionV(W::RngOrdIdl, W2::RngOrdIdl: GroupType := "GL2+") -> RngOrdElt
{}
    ZF := Order(W);
    F := NumberField(ZF);

    //Get totally positive unit generating V
    v := FundamentalUnitTotPos(F);
    if GroupType eq "GL2+" then
        //Congruence conditions are simply on v; we can ignore W2.
        Q := quo<ZF|W>;
        U, Umap := UnitGroup(Q);
        k := Order((Q!v)@@Umap);
        V := v^k;
    elif GroupType eq "SL2" then
        //Output unit must be of the form w^2
        t, w := IsSquare(v);
        if not t then
            w := v;
            v := v^2;
        end if;
        Q := quo<ZF|W2>;
        U, Umap := UnitGroup(Q);
        k1 := Order((Q!v)@@Umap); //v^k1 = 1 mod W2
        Q := quo<ZF|W>;
        U, Umap := UnitGroup(Q);
        S, Smap := quo<U|[(Q!(-ZF!1))@@Umap]>;
        k2 := Order(Smap((Q!w)@@Umap)); // t^k2 = +-1 mod W
        V := v^Lcm(k1,k2);
    else
        error "GroupType not recognized:", GroupType;
    end if;
    return V;
end intrinsic;

intrinsic CuspResolutionMinimalSequence(M :: RngOrdFracIdl) -> SeqEnum[RngIntElt]
{Compute the periodic part of the HJ continued fraction, as in Van der Geer p.38}
    require M ne 0*M: "Module M must not be zero";

    F := NumberField(Order(M));
    a,b := OrientedBasis(M);

    head, periodic := HJContinuedFraction(F ! (a/b));
    return periodic;
end intrinsic;

intrinsic OrientedBasis(M :: RngOrdFracIdl) -> Any
{}
    a, b := Explode(Basis(M));
    F := NumberField(Order(M));
    fa := F ! a;
    fb := F ! b;
    _, ori := Explode(Eltseq(fa * QuadraticConjugate(fb) - fb * QuadraticConjugate(fa)));
    if ori lt 0 then
        return b, a;
    else
        return a, b;
    end if;
end intrinsic;

intrinsic CuspResolutionMinimalUnit(F :: FldNum, per :: SeqEnum[RngIntElt]) -> FldNumElt
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

// this is the top-level function
intrinsic CuspResolutionIntersections(G::GrpHilbert, p::Pt) -> SeqEnum, RngIntElt
{}
    K := BaseField(G);
    N := Level(G);
    b := Component(G);
    x, y := Explode(Coordinates(p));
    x, y := NormalizeCusp(b, N, x, y);
    if AmbientType(G) eq GLPlus_Type then
        GroupType := "GL2+";
    elif AmbientType(G) eq SL_Type then
        GroupType := "SL2";
    else
        error "Ambient type not recognized:", AmbientType(G);
    end if;
    return CuspResolutionIntersections(Component(G), N, x, y :
                                       GammaType:=GammaType(G),
                                       GroupType:=GroupType);
end intrinsic;

intrinsic CuspResolutionIntersections(G::GrpHilbert, alpha::FldNumElt, beta::FldNumElt)
          -> SeqEnum, RngIntElt
{}
    K := BaseField(G);
    P := ProjectiveSpace(K,1);
    return CuspResolutionIntersections(G, P![alpha,beta]);
end intrinsic;

intrinsic CuspResolutionIntersections(b :: RngOrdFracIdl, n :: RngOrdIdl,
                                      alpha :: FldNumElt, beta::FldNumElt
                                      : GammaType := "Gamma0", GroupType := "GL2+")
          -> SeqEnum[RngIntElt], RngIntElt

{Compute the cyclic sequence of self-intersection numbers for the cycle of P1's
appearing in the appearing in the resolution of the cusp (alpha:beta) in P^1(F)
for the specified modular group. Accepted values for the parameter GammaType
are: "Gamma0" (default); "Gamma1"; "Gamma" (full level); and "GammaP" for
Ker(Gamma(1)->PSL(ZF/n)), in the case GroupType:="SL2", for testing purposes.}

    require IsNormalizedCusp(b, n, alpha, beta): "Cusp (alpha,beta) must be normalized";

    ZF := Order(b);
    F := NumberField(ZF);
    M, V, g := CuspResolutionMV(b, n, alpha, beta:
                                   GammaType := GammaType, GroupType:=GroupType);
    periodic := CuspResolutionMinimalSequence(M);
    w := CuspResolutionMinimalUnit(F, periodic);
    U, Umap := UnitGroup(ZF);
    S, Smap := quo<U|V@@Umap>;
    k := Order(Smap(w@@Umap)); //k minimal such that w^k\in V

    L := [-b: b in periodic];
    if #L eq 1 and k eq 1 then L := [L[1]+2]; end if;
    return CanonicalCyclicShift(L), k;
end intrinsic;

/* ------------------------------------------------------------------------- */
/* Testing */

intrinsic IsInGMV(M::RngOrdFracIdl, V::RngOrdElt, g :: AlgMatElt) -> Bool
{True iff g belongs to G(M,V) as a transformation (i.e. up to multiplication by a scalar matrix)}
    require IsUnit(V) and IsTotallyPositive(V): "V must be generated by a totally positive unit";

    ZF := Order(M);
    F := NumberField(ZF);
    U, Umap := UnitGroup(ZF);
    S := sub<U|V@@Umap>;
    if g[2,2] eq 0 or g[2,1] ne 0 then return false; end if;
    v := g[1,1]/g[2,2];
    m := g[2,1]/g[2,2];
    if not IsUnit(v) and IsTotallyPositive(v) then return false; end if;
    return m in M and v@@Umap in S;
end intrinsic;

intrinsic IsInLevelSubgroup(b::RngOrdFracIdl, n::RngOrdIdl, g::AlgMatElt:
                            GammaType := "Gamma0", GroupType := "GL2+") -> Bool
{True iff g belongs to the specified modular group as a transformation (i.e. up to multiplication by a scalar matrix)}
    ZF := Order(b);
    F := NumberField(ZF);
    w := FundamentalUnit(F);
    if not IsTotallyPositive(w) and IsTotallyPositive(-w) then w:=-w; end if;

    //First scale by scalar matrix such that determinant is a tot. pos. unit (or 1)
    d := Determinant(g);
    if not IsTotallyPositive(d) then return false; end if;
    if GroupType eq "GL2+" then
        t1, r1 := IsSquare(d);
        t2, r2 := IsSquare(w*d);
        if t1 then
            g := (1/r1) * g;
        elif t2 then
            g := (1/r2) * g;
        else
            return false; //Determinant is not a square mod totally positive units
        end if;
        d := Determinant(g);
        assert IsUnit(d) and IsTotallyPositive(d);
    elif GroupType eq "SL2" then
        t, r := IsSquare(d);
        if t then
            g := (1/r) * g;
        else
            return false; //Determinant is not a square
        end if;
        d := Determinant(g);
        assert d eq 1;
    else
        error "GroupType not recognized:", GroupType;
    end if;

    //We can still multiply g by any unit in the GL2+ case, and by -1 in the SL2 case
    //In any case, matrix must belong to Gamma_b and lower left entry must be 0 mod N
    if not (g[1,1] in ZF and g[2,2] in ZF and g[1,2] in b^(-1) and g[2,1] in n*b) then
        return false;
    end if;
    //Then diagonal entries of g must be invertible mod n.
    //In the Gamma0 case, we can already return true.
    if GammaType eq "Gamma0" then
        return true;
    end if;

    if GroupType eq "GL2+" then
        if GammaType eq "Gamma1" then
            return IsUnitModIdeal(n, g[1,1]);
        elif GammaType eq "Gamma" then
            return IsUnitModIdeal(n, g[1,1]) and g[1,2] in n*b^(-1) and g[2,2]-g[1,1] in n;
        else
            error "GammaType not recognized:", GammaType;
        end if;
    elif GroupType eq "SL2" then
        if not g[1,1]-1 in n then g := -g; end if;
        if GammaType eq "Gamma1" then
            return g[1,1]-1 in n;
        elif GammaType eq "Gamma" then
            return g[1,1]-1 in n and g[1,2] in n*b^(-1) and g[2,2]-1 in n;
        else
            error "GammaType not recognized:", GammaType;
        end if;
    end if;
end intrinsic;

intrinsic SamplesOfLevelSubgroup(b::RngOrdFracIdl, n::RngOrdIdl:
                                 GammaType := "Gamma0", GroupType := "GL2+")
          -> SeqEnum[AlgMatElt]
{Return a list of matrices belonging to the specified level subgroup}
    //First generate matrices in SL2; then multiply on the right by [1,0;0,v] if in GL2+
    ZF := Order(b);
    F := NumberField(ZF);
    BZ := Basis(ZF);
    BN := Basis(n);
    BNb := Basis(n*b);
    BNb1 := Basis(n*b^(-1));
    Bb1 := Basis(b^(-1));
    w := FundamentalUnit(F);
    Q := quo<ZF|n>;
    U, Umap := UnitGroup(Q);
    k := Order((Q!w)@@Umap); //Order of w modulo n
    list := [];

    if GammaType eq "Gamma0" then
        Append(~list, Matrix(F, [[1,0],[BNb[1],1]]));
        Append(~list, Matrix(F, [[1,0],[BNb[2],1]]));
        Append(~list, Matrix(F, [[1, Bb1[1]],[0,1]]));
        Append(~list, Matrix(F, [[1, Bb1[2]],[0,1]]));
        Append(~list, Matrix(F, [[w,0],[0,w^(-1)]]));
        Append(~list, Matrix(F, [[-1,0],[0,-1]]));
    elif GammaType eq "Gamma1" then
        Append(~list, Matrix(F, [[1,0],[BNb[1],1]]));
        Append(~list, Matrix(F, [[1,0],[BNb[2],1]]));
        Append(~list, Matrix(F, [[1, Bb1[1]],[0,1]]));
        Append(~list, Matrix(F, [[1, Bb1[2]],[0,1]]));
        Append(~list, Matrix(F, [[w^k,0],[0,w^(-k)]]));
    elif GammaType eq "Gamma" then
        Append(~list, Matrix(F, [[1,0],[BNb[1],1]]));
        Append(~list, Matrix(F, [[1,0],[BNb[2],1]]));
        Append(~list, Matrix(F, [[1, BNb1[1]],[0,1]]));
        Append(~list, Matrix(F, [[1, BNb1[2]],[0,1]]));
        Append(~list, Matrix(F, [[w^k,0],[0,w^(-k)]]));
    else
        error "GammaType not recognized:", GammaType;
    end if;

    if GroupType eq "GL2+" then
        u := FundamentalUnitTotPos(F);
        if GammaType eq "Gamma0" or GammaType eq "Gamma1" then
            Append(~list, Matrix(F, [[1,0],[0,u]]));
        else
            k := Order((Q!u)@@Umap); //Order of u modulo n
            Append(~list, Matrix(F, [[1,0],[0,u^k]]));
        end if;
    elif GroupType ne "SL2" then
        error "GroupType not recognized:", GroupType;
    end if;
    return list;
end intrinsic;

intrinsic SamplesOfLevelSubgroupInStabilizer(b::RngOrdFracIdl, n::RngOrdIdl,
                                             alpha::FldNumElt, beta::FldNumElt:
                                             GammaType := "Gamma0", GroupType := "GL2+")
          -> SeqEnum[AlgMatElt]
{Return a list of matrices belonging to the specified level subgroup that
stabilize the given cusp in P^1(F)}

    //TODO for stronger tests if problems happen

end intrinsic;

intrinsic GeneratorsOfGMV(M::RngOrdFracIdl, V::RngOrdElt) -> SeqEnum[AlgMatElt]
{Return three matrices that generate G(M,V) as a group}
    require IsUnit(V) and IsTotallyPositive(V): "V must be generated by a totally positive unit";
    ZF := Order(M);
    F := NumberField(ZF);
    x, y := Explode(Basis(M));
    U1 := Matrix(F, 2, 2, [V, F!0, F!0, F!1]);
    U2 := Matrix(F, 2, 2, [F!1, x, F!0, F!1]);
    U3 := Matrix(F, 2, 2, [F!1, y, F!0, F!1]);
    return [U1, U2, U3];
end intrinsic;

