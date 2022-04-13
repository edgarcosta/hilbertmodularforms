freeze;

declare attributes AlgAssV : MaximalOrderInfinite;

intrinsic ZBasis(O::AlgAssVOrd[RngFunOrd]) -> SeqEnum
{A basis for the order O as a free Z-module}

    return ZBasis(PseudoMatrix(O), Algebra(O));
end intrinsic;



function algebraic_maximal_order(A, R, max_ord)
    B, m := RestrictionOfScalars(A, R);
    MB := max_ord(B);
    bMB := [b @@ m : b in Basis(MB)];
    mbMB := Matrix(bMB);
    assert Rank(mbMB) eq Dimension(A);
    assert B!1 in MB;
    mbMB := VerticalJoin(A!1, mbMB);

    mobra := max_ord(BaseRing(A));
    pm := PseudoMatrix([1*mobra : i in [1 .. Nrows(mbMB)]], Matrix(FieldOfFractions(mobra), mbMB));
    M := Order(A, HermiteForm(pm));
    return M;

    E := EchelonForm(Transpose(mbMB));
    P := [];
    for i := 1 to Nrows(E) do
        S := Support(E[i]);
        if #S gt 0 then
            Append(~P, Min(S));
        end if;
    end for;
    mbMB := Matrix(mbMB[P]);

    return Order(A, mbMB, [PowerIdeal(MaximalOrder(BaseRing(A))) | 1 : i in [1 .. Dimension(A)]]);
    return Order(bMB);
end function;

intrinsic MaximalOrder(A::AlgAss[FldAlg]) -> AlgAssVOrd
{The maximal order of the associative algebra A}
    if assigned A`MaximalOrder then
	return A`MaximalOrder;
    end if;

    M := algebraic_maximal_order(A, Rationals(), MaximalOrder);
    A`MaximalOrder := M;
    return M;
end intrinsic;

intrinsic MaximalOrderFinite(A::AlgAss[FldFun]) -> AlgAssVOrd
{The maximal order of the associative algebra A}
    if assigned A`MaximalOrder then
	return A`MaximalOrder;
    end if;

    require Dimension(A) mod Characteristic(A) ne 0 : "Dimension of the algebra must be non-zero mod the characteristic of the algebra";

    require AbsoluteDegree(CoefficientField(A)) mod Characteristic(A) ne 0 : "Absolute degree of the coefficient field of the algebra must be non-zero mod the characteristic of the algebra";

    F := FiniteExtensionRepresentation(BaseRing(A));
    while Type(F) eq FldFun do
	F := CoefficientField(F);
    end while;
    assert Type(F) eq FldFunRat;
    M := algebraic_maximal_order(A, F, MaximalOrderFinite);
    A`MaximalOrder := M;
    return M;
end intrinsic;

intrinsic MaximalOrderInfinite(A::AlgAss[FldFun]) -> AlgAssVOrd
{The maximal order of the associative algebra A}
    if assigned A`MaximalOrderInfinite then
	return A`MaximalOrderInfinite;
    end if;

    require Dimension(A) mod Characteristic(A) ne 0 : "Dimension of the algebra must be non-zero mod the characteristic of the algebra";

    require AbsoluteDegree(CoefficientField(A)) mod Characteristic(A) ne 0 : "Absolute degree of the coefficient field of the algebra must be non-zero mod the characteristic of the algebra";

    F := FiniteExtensionRepresentation(BaseRing(A));
    while Type(F) eq FldFun do
	F := CoefficientField(F);
    end while;
    assert Type(F) eq FldFunRat;
    M := algebraic_maximal_order(A, F, MaximalOrderInfinite);
    A`MaximalOrderInfinite := M;
    return M;
end intrinsic;

function AlgAssV_maximal_order(A, max_ord)
    AA, m := Algebra(A);
    MAA := max_ord(AA);
    pb := PseudoBasis(MAA);
    pbi := [b[1] : b in pb];
    pbm := [Eltseq(b[2] @@ m) : b in pb];
    pm := PseudoMatrix(pbi, Matrix(pbm));
    M := Order(A, HermiteForm(pm));
    return M;
end function;

intrinsic MaximalOrder(A::AlgAssV[FldAlg]) -> AlgAssVOrd
{The maximal order of the associative algebra A}
    if assigned A`MaximalOrder then
	return A`MaximalOrder;
    end if;

    M := AlgAssV_maximal_order(A, MaximalOrder);
    A`MaximalOrder := M;
    return M;
end intrinsic;

intrinsic MaximalOrderFinite(A::AlgAssV[FldFun]) -> AlgAssVOrd
{The maximal order of the associative algebra A}
    if assigned A`MaximalOrder then
	return A`MaximalOrder;
    end if;

    M := AlgAssV_maximal_order(A, MaximalOrderFinite);
    A`MaximalOrder := M;
    return M;
end intrinsic;

intrinsic MaximalOrderInfinite(A::AlgAssV[FldFun]) -> AlgAssVOrd
{The maximal order of the associative algebra A}
    if assigned A`MaximalOrderInfinite then
	return A`MaximalOrderInfinite;
    end if;

    M := AlgAssV_maximal_order(A, MaximalOrderInfinite);
    A`MaximalOrderInfinite := M;
    return M;
end intrinsic;

function order_maximal_order(O, A, R)
    B, _, m := RestrictionOfScalars(O, R);
    MB := MaximalOrder(B);		//DIDN'T HAVE THIS!@!!!!
    bMB := [A!(b @@ m) : b in Basis(MB)];
    mbMB := Matrix(bMB);
    assert Rank(mbMB) eq Dimension(O);
    assert B!1 in MB;
    mbMB := VerticalJoin(A!1, mbMB);

    pm := PseudoMatrix(Matrix(FieldOfFractions(BaseRing(O)), mbMB));
    M := Order(A, HermiteForm(pm));
    return M;
end function;

import "../AlgQuat/maxorder.m":QuaternionMaximalOrder;

intrinsic MaximalOrder(O::AlgAssVOrd[RngOrd]) -> AlgAssVOrd
{A maximal order containing O};

    if assigned O`IsMaximal and O`IsMaximal then
	return O;
    end if;

    A := Algebra(O);

    if assigned A`MaximalOrder and &and[x in A`MaximalOrder : x in ZBasis(O)] then
	return A`MaximalOrder;
    end if;

    if ISA(Type(A), AlgQuat) and CoefficientRing(CoefficientRing(O)) cmpeq Integers() then
	return QuaternionMaximalOrder(O);
    end if;
    M := order_maximal_order(O, A, Integers());
    if not assigned A`MaximalOrder then
	A`MaximalOrder := M;
    end if;
    return M;
end intrinsic;

intrinsic MaximalOrder(O::AlgAssVOrd[RngFunOrd]) -> AlgAssVOrd
{A maximal order containing O};

    if assigned O`IsMaximal and O`IsMaximal then
	return O;
    end if;

    A := Algebra(O);

    if assigned A`MaximalOrder and (CoefficientRing(O) cmpeq CoefficientRing(A`MaximalOrder)) and &and[x in A`MaximalOrder : x in ZBasis(O)] then
	return A`MaximalOrder;
    end if;

    if assigned A`MaximalOrderInfinite and (CoefficientRing(O) cmpeq CoefficientRing(A`MaximalOrderInfinite)) and &and[x in A`MaximalOrderInfinite : x in ZBasis(O)] then
	return A`MaximalOrderInfinite;
    end if;

    R := CoefficientRing(O);
    while Type(R) eq RngFunOrd do
	R := CoefficientRing(R);
    end while;
    return order_maximal_order(O, A, R);
end intrinsic;

function restrict_scalars_order(O, C)
    OC := BaseRing(O);
    if IsIdentical(OC, C) then
	return O, IdentityHomomorphism(O);
    end if;

    BRb := Basis(OC);
    while not IsIdentical(BaseRing(OC), C) and Type(BaseRing(OC)) notin {RngUPol, RngInt} do
	OC := BaseRing(OC);
	BRb := [x*y : x in BRb, y in Basis(OC)];
    end while;

    error if not IsIdentical(BaseRing(OC), C),
        "Argument 2 is not a coefficient ring of the base ring of Argument 1";

    A := Algebra(O);
    B, m := RestrictionOfScalars(A, FieldOfFractions(C));
    pbo := PseudoBasis(O);

    b := &cat[[e1*xy, e2*xy] where xy := x[2]*y where e1, e2 := TwoElement(x[1]) : x in pbo, y in BRb];
    b := [bb @ m : bb in b];
    mb := Matrix(b);
    assert Rank(mb) eq Dimension(B);
    assert A!1 in O;
    mb := VerticalJoin(B!1, mb);

    if ISA(Type(C), RngOrd) or Type(C) eq RngFunOrd then
	pm := PseudoMatrix(Matrix(FieldOfFractions(MaximalOrder(C)), mb));
	OB := Order(B, HermiteForm(pm));
    else
	if Type(C) eq RngVal then
	    val := Maximum([Valuation(x, C!(1/FieldOfFractions(C).1)) : x in Eltseq(mb) | x ne 0]);
	    den := 1/FieldOfFractions(C).1^-Minimum(0, val);
	else
	    den := Denominator(mb);
	end if;
	mb := Matrix(C, den*mb);
	mb := HermiteForm(mb);
	assert Rank(mb) eq Dimension(B);
	mb := Submatrix(mb, 1, 1, Dimension(B), Dimension(B));
	mb *:= 1/den;
	b := [B!mbi : mbi in Rows(mb)];
	OB := Order(C, b);
    end if;

    return OB, map<O -> OB | x :-> m(x), y :-> y @@ m>, m;

end function;

intrinsic RestrictionOfScalars(O::AlgAssVOrd[RngOrd], C::Rng) -> AlgAssVOrd, Map
{Given an order O, return an isomorphic order over the ring C}
    return restrict_scalars_order(O, C);
end intrinsic;

intrinsic RestrictionOfScalars(O::AlgAssVOrd[RngFunOrd], C::Rng) -> AlgAssVOrd, Map
{Given an order O, return an isomorphic order over the ring C}
    return restrict_scalars_order(O, C);
end intrinsic;

intrinsic RestrictionOfScalars(O::AlgAssVOrd[RngOrd]) -> AlgAssVOrd, Map
{Given an order O over a ring R, return an isomorphic order over BaseRing(R)}
    return RestrictionOfScalars(O, BaseRing(BaseRing(O)));
end intrinsic;

intrinsic RestrictionOfScalars(O::AlgAssVOrd[RngFunOrd]) -> AlgAssVOrd, Map
{Given an order O over a ring R, return an isomorphic order over BaseRing(R)}
    return RestrictionOfScalars(O, BaseRing(BaseRing(O)));
end intrinsic;

/*
SetDebugOnError(true);
A := AssociativeAlgebra(A);   
O := Order([A | alpha, beta]);
Norm(Discriminant(O))*Discriminant(BaseRing(O))^Dimension(O);
RestrictionOfScalars(O);
Discriminant($1);

RestrictionOfScalars(MaximalOrder(Algebra(O)));
Discriminant($1);
Norm(Discriminant(MaximalOrder(Algebra(O))))*Discriminant(BaseRing(O))^Dimension(O);

MaximalOrder(Algebra(RestrictionOfScalars(O)));
Discriminant($1);

MaximalOrder(RestrictionOfScalars(A));
Discriminant($1);
RestrictionOfScalars(MaximalOrder(A));
Discriminant($1);



P<x> := PolynomialRing(RationalsAsNumberField());
F<b> := NumberField(x^3-3*x-1);
Z_F := MaximalOrder(F);
A<alpha,beta,alphabeta> := QuaternionAlgebra<F | -3,b>;
A := AssociativeAlgebra(A);
RestrictionOfScalars(A);
RestrictionOfScalars(A, Rationals());
O := Order([A|alpha,beta]);
RestrictionOfScalars(O);
Discriminant($1);
Norm(Discriminant(O))*Discriminant(BaseRing(O))^Dimension(O);
RestrictionOfScalars(O, Integers());
Discriminant($1);
Discriminant(BaseRing(BaseRing(O)));
RestrictionOfScalars(MaximalOrder(Algebra(O)));
>

Total time: 0.450 seconds, Total memory usage: 32.09MB
hugo:/magma/nicole/libs/examples> magma H82E5
*/
