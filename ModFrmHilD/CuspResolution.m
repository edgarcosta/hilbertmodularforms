
intrinsic IsCoprime(a :: RngQuadFracIdl, b :: RngFracIdl) -> Bool
{Decide if fractional ideals a and b are coprime}
    if a eq 0*a or b eq 0*b then return false;
    end if;
    primes_a := [f[1] : f in Factorization(a)];
    primes_b := [f[1] : f in Factorization(b)];
    for p in primes_a do
	if p in primes_b then return false;
	end if;
    end for;
    return true;
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
