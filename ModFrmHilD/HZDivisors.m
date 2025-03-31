function R1(D,N)
    return [p : p in PrimeDivisors(D) | N mod p ne 0 ];
end function;

function R2(D,N)
    return [p : p in PrimeDivisors(D) | Valuation(N,p) ge 2*Valuation(D,p) ];
end function;

intrinsic PrimeDiscriminant(D::RngIntElt,q::RngIntElt) -> RngIntElt
{Return the prime discriminant D(q).}
    require D mod q eq 0 : "q must divide D.";
    require IsFundamentalDiscriminant(D) : "D must be a fundamental discriminant.";
    require IsPrime(q) : "q must be a prime.";
    sign := (q mod 4 eq 1) select 1 else -1;
    if (q eq 2) then
	sign := (-1)^(#[p : p in PrimeDivisors(D) | p mod 4 eq 3]);
    end if;
    return sign*q^Valuation(D,q);
end intrinsic;

function IsHZEmpty(Gamma,N)
    D := Discriminant(BaseField(Gamma));
    b := Component(Gamma);
    R1_primes := R1(D,N);
    for q in R1_primes do
	Dq := PrimeDiscriminant(D,q);
	chi := KroneckerCharacter(Dq);
	hilb := HilbertSymbol(Norm(b), D, q);
	if (chi(N) ne hilb) then
	    return true;
	end if;
    end for;
    return false;
end function;

// For some reason, these are not supported in Magma

// This could be made more efficient. For now using a simple implementation.
intrinsic IsPrimePower(I::RngOrdIdl) -> BoolElt
{True if I is a power of a prime ideal.}
  return #Factorization(I) eq 1;
end intrinsic;

intrinsic Sqrt(x::RngOrdResElt) -> RngOrdResElt
{The square root of x.}
  ZF_mod_N := Parent(x);
  N := Modulus(ZF_mod_N);	 
  require IsPrimePower(N) : "At the moment only supports prime powers";
  ZF := Order(N);
  frakp := Factorization(N)[1][1];
  ZFp, comp_p := Completion(ZF, frakp);
  pi := UniformizingElement(ZFp);
  // This is to handle the p = 2 case
  sqr := comp_p(ZF!x);
  if IsSquare(sqr) then
      sqrt_xp := Sqrt(sqr);
  else
      val_N := Valuation(N, frakp);
      sqr +:= pi^val_N;
      if IsSquare(sqr) then
	  sqrt_xp := Sqrt(sqr);
      else
	  // This is the case p = 2.
	  // Here I just give up and brute force my way for now
	  assert exists(sqrt_x){y : y in ZF_mod_N | y^2 eq x};
	  return sqrt_x;
	  /*
	  v := Valuation(sqr);
	  assert (v gt 0) and IsEven(v);
	  sqr div:= pi^v;
	  ZF_mod_NN, red_NN := quo<ZF | frakp^(val_N - v)>;
	  t := Sqrt(ZF_mod_NN!(((quo<ZFp | pi^(val_N - v)>)!sqr)@@comp_p));
	  sqrt_xp := pi^(v div 2)*comp_p(ZF!t);
	  */
      end if;
  end if;
  sqrt_x := Parent(x)!((sqrt_xp + O(pi^Valuation(N,frakp)))@@comp_p);
  assert sqrt_x^2 eq x;
  return sqrt_x;
end intrinsic;

intrinsic GetPossibleThetas(Gamma::GrpHilbert, N::RngIntElt) -> SeqEnum[Assoc]
{Get the possible values of the invariants theta = theta_p for p in R1 for the HZ divisor F_N.}
    require not IsHZEmpty(Gamma,N) : "The image of F_N in X_Gamma is empty!";
    D := Discriminant(Integers(BaseField(Gamma)));
    b := Component(Gamma);
    ZF := Order(b);
    F := NumberField(ZF);
    R1_primes := R1(D,N);
    all_thetas := AssociativeArray(R1_primes);
    if IsEmpty(R1_primes) then return [all_thetas]; end if;
    for p in R1_primes do
	v := Valuation(D,p);
	frakp := PrimeIdealsOverPrime(F,p)[1];
	ZFmodpv, red := quo<ZF | frakp^Valuation(D,p)>;
	if (p eq 2) and (v eq 2) then
	    d := SquareFree(D);
	    thetas := [1, Sqrt(ZF!d)];
	else
	    x := Sqrt(ZFmodpv!Norm(b)*N)@@red;
	    thetas := [x, -x];
	end if;
	all_thetas[p] := thetas;
    end for;
    thetas := [];
    for theta in CartesianProduct([all_thetas[p] : p in R1_primes]) do
	theta_assoc := AssociativeArray(R1_primes);
	for i->p in R1_primes do
	    theta_assoc[p] := theta[i];
	end for;
	Append(~thetas,theta_assoc);
    end for;
    return thetas;
end intrinsic;

intrinsic GetPossibleEtas(Gamma::GrpHilbert, N::RngIntElt) -> SeqEnum[Assoc]
{Get the possible values of the invariants eta = eta_p for p in R2 for the HZ divisor F_N.}
    require not IsHZEmpty(Gamma,N) : "The image of F_N in X_Gamma is empty!";
    D := Discriminant(Integers(BaseField(Gamma)));
    R2_primes := R2(D,N);
    all_etas := AssociativeArray(R2_primes);
    if IsEmpty(R2_primes) then return [all_etas]; end if;
    F := BaseField(Gamma);
    ZF := Integers(F);
    for p in R2_primes do
	// frakp := PrimeIdealsOverPrime(F,p)[1];
	if (p eq 2) then
	    // ZF_mod_pv, red := quo<ZF | frakp^Valuation(D,2)>
	    // all_etas[p] := [ZF | 1, 3];
	    all_etas[p] := [Integers() | 1, 3];
	else
	    // ZF_mod_pv, red := ResidueClassField(frakp);
	    // all_etas[p] := [ZF| 1, Nonsquare(GF(p))@@red];
	    all_etas[p] := [Integers() | 1, Integers(p)!Nonsquare(GF(p))];
	end if;
    end for;
    etas := [];
    for eta in CartesianProduct([all_etas[p] : p in R2_primes]) do
	eta_assoc := AssociativeArray(R2_primes);
	for i->p in R2_primes do
	    eta_assoc[p] := eta[i];
	end for;
	Append(~etas,eta_assoc);
    end for;
    return etas;
end intrinsic;

function find_a(eta, D, bb, N)
    R2_primes := [x : x in Keys(eta)];
    eta_vals := [eta[x] : x in R2_primes];
    // The 2 is not necessary, but we would like to avoid complications arising at 2
    a_prime_to := [p : p in PrimeDivisors(2*D*N*Norm(bb)) | p notin R2_primes];
    a := CRT(eta_vals cat [1 : p in a_prime_to], R2_primes cat a_prime_to);
    return a;
end function;

function find_mu(theta, eta, a, D, bb, N)
    ZF := Order(bb);
    F := NumberField(ZF);
    R1_primes := R1(D,N);
    R2_primes := R2(D,N);
    other_primes := [p : p in PrimeDivisors(D) | p notin R1_primes cat R2_primes];
    a_primes := [p : p in PrimeDivisors(a)];
    values := [ZF | 0];
    ideals := [Conjugate(bb)];
    values cat:= [theta[p] : p in R1_primes];
    ideals cat:= [PrimeIdealsOverPrime(F,p)[1]^Valuation(D,p) : p in R1_primes];
    values cat:= [0 : p in R2_primes];
    ideals cat:= [p^Valuation(D,p)*ZF : p in R2_primes];
    // TODO: Figure out what happens for p = 2 in other_primes !!
    for p in other_primes do
	frakp := PrimeIdealsOverPrime(F,p)[1];
	ZFmodpv, red := quo<ZF | frakp^Valuation(D,p)>;
	Append(~values, Sqrt(red(N*Norm(bb))));
	Append(~ideals, frakp^Valuation(D,p));
    end for;
    for p in a_primes do
	frakps := PrimeIdealsOverPrime(F,p);
	frakp := frakps[1];
	ZFmodpv, red := quo<ZF | frakp^Valuation(a,p)>;
	if #frakps eq 1 then
	    // inert case
	    // We assume p ne 2 since we can choose a this way
	    U, mU := MultiplicativeGroup(ZFmodpv);
	    Fq := GF(p^2);
	    zeta := PrimitiveElement(Fq);
	    h := hom<ZF -> Fq | zeta^(Eltseq(red(ZF.2)@@mU)[1]) >;
	    h_inv := hom<Fq -> ZFmodpv | mU(U.1)>;
	    // For some reason this doesn't work. However, we can solve it by hands quite simply
	    // is_norm, sol := NormEquation(Fq, h(N*Norm(bb)));
	    // assert is_norm;
	    t := h(N*Norm(bb));
	    Fp := PrimeField(Fq);
	    is_sqr, sol := IsSquare(Fp!t);
	    if is_sqr then
		sol := Fq!sol;
	    else
		is_sqr, sol := IsSquare(Norm(zeta)*Fp!t);
		assert is_sqr;
		sol := zeta * Fq!sol;
	    end if;
	    Append(~values, h_inv(sol)@@red);
	    Append(~ideals, frakp^Valuation(a,p));
	else
	    // split case
	    values cat:= [N*Norm(bb), 1];
	    ideals cat:= [frakp^Valuation(a,p), frakps[2]^Valuation(a,p)];
	end if;	
    end for;
    mu := CRT(values, ideals);
    assert ((Norm(mu) - N*Norm(bb)) mod a*D*Norm(bb)) eq 0;
    return mu;
end function;

intrinsic GetHZComponent(Gamma::GrpHilbert, theta::Assoc, eta::Assoc, N::RngIntElt) -> Mtrx
{Returns a matrix B, such that F_B is a component of F_N on X_Gamma with invariants theta, eta.}	  
    bb := Component(Gamma);
    ZF := Order(bb);
    F := NumberField(ZF);
    D := Discriminant(ZF);
    sigma := Automorphisms(F)[2];
    sqrtD := Sqrt(F!D);
    a := find_a(eta, D, bb, N);
    mu := find_mu(theta, eta, a, D, bb, N);
    b := (N*Norm(bb) - Norm(mu)) div (a*Norm(bb)*D);
    lambda := Norm(bb)^(-1) * mu;
    // Verifying we have an admissible matrix B
    R2_primes := [x : x in Keys(eta)];
    assert lambda in bb^(-1);
    assert &and[GCD(a,p) eq 1 : p in R2_primes];
    assert &and[Norm(bb)*lambda in p^Valuation(D,p)*ZF : p in R2_primes];
    assert &and[b mod p^Valuation(D,p) eq 0 : p in R2_primes];
    g := GCD(a,b);
    if (g gt 1) then
	assert g^(-1)*lambda notin bb^(-1);
    end if;
    B := Matrix([[a*sqrtD, lambda], [-sigma(lambda), Norm(bb)^(-1)*b*sqrtD]]);
    return B;
end intrinsic;

function is_minus_in_orbit(Gamma, N)
    bb := Component(Gamma);
    ZF := Order(bb);
    F := NumberField(ZF);
    D := Discriminant(ZF);
    d := SquareFree(D);
    not_in_theta := exists(p){p : p in R1(D,N) | d mod p eq 0};
    if not_in_theta then
	return false, "theta", p;
    end if;
    not_in_eta := exists(p){p : p in R2(D,N) | HilbertSymbol(-1,D,p) eq -1};
    if not_in_eta then
	return false, "eta", p;
    end if;
    return true, _, _;
end function;

intrinsic GetAllHZComponents(Gamma::GrpHilbert, N::RngIntElt) -> SeqEnum[AlgMatElt[FldNum]]
{Returns a list of matrices B, such that F_B are representatives for the components of F_N on X_Gamma.}
    if IsHZEmpty(Gamma,N) then
	return [];
    end if;
    ZF := Order(Component(Gamma));
    require Level(Gamma) eq 1*ZF : "Currently only supports trivial level.";
    require AmbientType(Gamma) eq SL_Type : "Currently only supports SL type.";
    thetas := GetPossibleThetas(Gamma,N);
    etas := GetPossibleEtas(Gamma,N);
    is_minus,part,p := is_minus_in_orbit(Gamma,N);
    if not is_minus then
	if (part eq "theta") then
	    theta_p := [x : x in {theta[p] : theta in thetas}];
	    thetas := [theta : theta in thetas | theta[p] eq theta_p[1]];
	else
	    eta_p := [x : x in {eta[p] : eta in etas}];
	    etas := [eta : eta in etas | eta[p] eq eta_p[1]];
	end if;
    end if;
    comps := [GetHZComponent(Gamma, theta, eta,  N) : theta in thetas,
						      eta in etas];
    assert &and[not IsSameComponent(Gamma, comps[i], comps[j])
		: i,j in [1..#comps] | i ne j];
    return comps;
end intrinsic;

intrinsic Theta(Gamma::GrpHilbert, B::AlgMatElt[FldNum]) -> SeqEnum[Assoc]
{Return the theta invariant of F_B on X_Gamma.}
  bb := Component(Gamma);
  N := Integers()! (Determinant(B)*Norm(bb));
  ZF := Order(bb);
  F := NumberField(ZF);
  sigma := Automorphisms(F)[2];
  D := Discriminant(ZF);
  lambda := B[1,2];
  require &and[B[i,j] eq -sigma(B[j,i]) : i,j in [1..2] | i lt j] : "B should be skew-Hermitian.";
  R1_primes := R1(D,N);
  theta := AssociativeArray(R1_primes);
  for p in R1_primes do
      frakp := PrimeIdealsOverPrime(F,p)[1];
      theta[p] := Norm(bb)*lambda;
  end for;
  return theta;
end intrinsic;

intrinsic IsThetaEqual(Gamma::GrpHilbert, theta1::Assoc, theta2::Assoc) -> BoolElt
{True if the two invariants are equal.}
  bb := Component(Gamma);
  ZF := Order(bb);
  F := NumberField(ZF);
  D := Discriminant(ZF);
  if Keys(theta1) ne Keys(theta2) then return false; end if;
  for p in Keys(theta1) do
      frakp := PrimeIdealsOverPrime(F,p)[1];
      v := Valuation(D,p);
      if Valuation(theta1[p] - theta2[p],frakp) lt v then
	  return false;
      end if;
  end for;
  return true;
end intrinsic;

intrinsic IsEtaEqual(Gamma::GrpHilbert, eta1::Assoc, eta2::Assoc) -> BoolElt
{True if the two invariants are equal.}
  bb := Component(Gamma);
  ZF := Order(bb);
  F := NumberField(ZF);
  D := Discriminant(ZF);
  if Keys(eta1) ne Keys(eta2) then return false; end if;
  for p in Keys(eta1) do
      hilb1 := HilbertSymbol(eta1[p], D, p);
      hilb2 := HilbertSymbol(eta2[p], D, p);
      if (hilb1 ne hilb2) then
	  return false;
      end if;
  end for;
  return true;
end intrinsic;

intrinsic Eta(Gamma::GrpHilbert, B::AlgMatElt[FldNum]) -> SeqEnum[Assoc]
{Return the theta invariant of F_B on X_Gamma.}
  bb := Component(Gamma);
  N := Integers()! (Determinant(B)*Norm(bb));
  ZF := Order(bb);
  F := NumberField(ZF);
  sigma := Automorphisms(F)[2];
  D := Discriminant(ZF);
  sqrtD := Sqrt(F!D);
  a := Integers()!(B[1,1] / sqrtD);
  b := Integers()!(B[2,2] * Norm(bb) / sqrtD);
  lambda := B[1,2];
  require &and[B[i,j] eq -sigma(B[j,i]) : i,j in [1..2] | i lt j] : "B should be skew-Hermitian.";
  R2_primes := R2(D,N);
  eta := AssociativeArray(R2_primes);
  for p in R2_primes do
      if GCD(a,p) eq 1 then
	  eta[p] := HilbertSymbol(a, D, p);
      elif Valuation(b,p) eq Valuation(Norm(bb),p) then
	  eta[p] := HilbertSymbol(b/Norm(bb), Rationals()!D, p);
      else
	  a_new := Rationals()! (a + b/Norm(bb) + (lambda - sigma(lambda)) / sqrtD);
	  assert Valuation(a_new, p) eq 0;
	  eta[p] := HilbertSymbol(a_new, Rationals()!D, p);
      end if;
  end for;
  return eta;
end intrinsic;

intrinsic IsSameComponent(Gamma::GrpHilbert, B1::AlgMatElt[FldNum], B2::AlgMatElt[FldNum]) -> BoolElt
{True if F_B1 and F_B2 belong to the same component on X_Gamma.}
  theta1 :=  Theta(Gamma, B1);
  theta2 := Theta(Gamma, B2);
  sgn := 1;
  eq_theta := IsThetaEqual(Gamma, theta1, theta2);
  if not eq_theta then
      sgn := -1;
      // we negate to check for a minus sign;
      for p in Keys(theta1) do
	  theta1[p] := sgn * theta1[p];
      end for;
      eq_theta := IsThetaEqual(Gamma, theta1, theta2);
      if not eq_theta then
	  return false;
      end if;
  end if;

  eta1 :=  Eta(Gamma, B1);
  eta2 := Eta(Gamma, B2);
  for p in Keys(eta1) do
      eta1[p] := sgn * eta1[p];
  end for;
  
  eq_eta := IsEtaEqual(Gamma, Eta(Gamma,B1), Eta(Gamma,B2));
  
  return eq_eta;
end intrinsic;	  

intrinsic GetHZComponent(Gamma::GrpHilbert, lambda::FldNumElt, comps::SeqEnum[AlgMatElt[FldNum]]) -> RngIntElt
{Return the index of the component F_B where B is a matrix corresponding to lambda with a = 0 on X_Gamma.}
  bb := Component(Gamma);
  ZF := Order(bb);
  F := NumberField(ZF);
  require Level(Gamma) eq 1*ZF : "Currently only supports trivial level.";
  require AmbientType(Gamma) eq SL_Type : "Currently only supports SL type.";
  sigma := Automorphisms(F)[2];
  D := Discriminant(ZF);
  sqrtD := Sqrt(F!D);
  B := Matrix([[0,lambda],[-sigma(lambda), sqrtD / Norm(bb)]]);
  for i->comp in comps do
      if IsSameComponent(Gamma, comp, B) then
	  return i;
      end if;
  end for;
  // This should not happen. If we're here something is wrong!!!
  return 0;
end intrinsic;	  

intrinsic Genera(R::RngOrd) -> Assoc
{Return a representative from each genus of the order.}
  cg, m_cg := ClassGroup(R);
  ncg, m_ncg := NarrowClassGroup(R);
  sq := hom<cg -> ncg | [(m_cg(cg.i)^2)@@m_ncg : i in [1..Ngens(cg)]] >;
  coset_reps := Transversal(ncg, Image(sq));
  ideals := [m_ncg(r) : r in coset_reps];
  symbs := [Genus(bb) : bb in ideals];
  genera := AssociativeArray(symbs);
  for i->symb in symbs do
      genera[symb] := ideals[i];
  end for;
  return genera;
end intrinsic;

intrinsic Genus(bb::RngOrdIdl) -> SeqEnum
{Return the signs representing the genus of the ideal bb.}
  D := Discriminant(Order(bb));
  return [HilbertSymbol(Norm(bb), D, q) : q in PrimeDivisors(D)];
end intrinsic;

intrinsic IsPrincipalGenus(bb::RngOrdIdl) -> BoolElt
{True if bb belongs to the principa genus of its order.}
  return Set(Genus(bb)) eq {1};
end intrinsic;

// This is not enough. In order to get components correctly in the presence of level structure, we should
// be able to construct explicit isometries transforming one Hermitian lattice to another, so that we will be
// able to check how they act on a distinguished line.

function bart(g)
    F := BaseRing(g);
    sigma := Automorphisms(F)[2];
    return Parent(g)![sigma(x) : x in Eltseq(Transpose(g))];
end function;

function Orthogonalize(C)
    assert (Nrows(C) eq 2) and (Ncols(C) eq 2);
    a := C[1,1];
    b := C[1,2];
    c := C[2,2];
    F := BaseRing(C);
    sigma := Automorphisms(F)[2];
    assert (C[2,1] eq sigma(b)) and (sigma(a) eq a) and (sigma(c) eq c);
    if (a eq 0) and (c eq 0) then
	T := Matrix(F, [[1,b],[1,-b]]);
    elif (a eq 0) then
	S := Matrix(F, [[0,1],[-1,0]]);
	_, T := Orthogonalize(S*C*bart(S));
	T := T*S;
    else
	T := Matrix(F, [[1,0],[-sigma(b),a]]); 
    end if;
    C_orth := T*C*bart(T);
    assert (C_orth[1,2] eq 0) and (C_orth[2,1] eq 0);
    return C_orth, T;
end function;

function FindIsometry(B1, B2)
    // we start by constructing lattices for both in the same Hermitian space
    F := BaseRing(B1);
    ZF := Integers(F);
    D := Discriminant(ZF);
    sqrtD := Sqrt(F!D);
    C1 := sqrtD*B1;
    C2 := sqrtD*B2;
    D1, T1 := Orthogonalize(C1);
    D2, T2 := Orthogonalize(C2);
    // !! TODO : Is that true? Maybe just away from the ramified primes? maybe up to a constant?
    assert D1 eq D2;
    bc := T1*T2^(-1);
    return bc;
end function;


