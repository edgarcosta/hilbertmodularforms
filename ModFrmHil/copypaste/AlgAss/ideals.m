freeze;

intrinsic Basis(I::AlgAssVOrdIdl, R::Str) -> SeqEnum
{The basis of the ideal as elements of R}

    ok, b := CanChangeUniverse(Basis(I), R);
    require ok : "Basis is not coercible into structure";
    return b;
end intrinsic;

intrinsic BasisMatrix(I::AlgAssVOrdIdl, R::Str) -> AlgMatElt
{The basis matrix of I with respect to the basis of R}

    b := BasisMatrix(I);
    if R cmpeq Order(I) then
        return b;
    end if;
    b *:= BasisMatrix(Order(I));
    if R cmpeq Algebra(I) then
        return b;
    end if;
    require ISA(Type(R), AlgAssVOrd) : "Structure is not compatible with ideal";
    require Algebra(I) cmpeq Algebra(R) : "Structure is not compatible with ideal";
    b *:= BasisMatrix(R)^-1;
    return b;

end intrinsic;

function ColonInternalZ(M1, M2, A, left)

    F := BaseField(A);
    FldFlat:= Type(F) in {FldRat, FldFunRat};
    Si := Matrix(F, M1)^-1;
    n := Nrows(Si);
    M := Matrix(F,0,n, []);

    for i in [1 .. n] do
        b := A!M2[i];
        if left then
            m := Transpose(RepresentationMatrix(b, Parent(b) : Side := "Right")*Si);
        else
            m := Transpose(RepresentationMatrix(b, Parent(b) : Side := "Left")*Si);
        end if;
        M := VerticalJoin(M, m);
    end for;

    den1 := FldFlat select LCM([Denominator(e)  :  e in Eltseq(M)])
                      else LCM([Denominator(ee) : ee in Eltseq(e), e in Eltseq(M)]);
    P := Matrix(F, HermiteForm(Matrix(Integers(F), den1*M)))/den1;
    M := Transpose(Submatrix(P, 1, 1, n, n))^-1;

    den1 := FldFlat select LCM([Denominator(e)  :  e in Eltseq(M)])
                      else LCM([Denominator(ee) : ee in Eltseq(e), e in Eltseq(M)]);
    return Matrix(F, HermiteForm(Matrix(Integers(F), den1*M)))/den1;

end function;

intrinsic '*'(I::AlgAssVOrdIdl, J::AlgAssVOrdIdl) -> AlgAssVOrdIdl, AlgAssVOrdIdl
{Product of associative ideals I and J};
    require RightOrder(I) cmpeq LeftOrder(J) : "Right order of the first argument must be equal to the left order of the second";

    O := Order(I);
    A := Algebra(O);
    F := BaseField(A);
    S := BaseRing(O);

    P := Matrix([A!x*A!y : x in Basis(I), y in Basis(J)]);
    den := Type(F) in {FldRat, FldFunRat}
              select LCM([Denominator(e)  :  e in Eltseq(P)])
                else LCM([Denominator(ee) : ee in Eltseq(e), e in Eltseq(P)]);
    P := HermiteForm(Matrix(S, den*P));
    P := Matrix(F, P)/den;
    P := RowSubmatrix(P, 1, Dimension(O));

    L := ColonInternalZ(P, P, A, true);
    R := ColonInternalZ(P, P, A, false);
    if L eq R then
        LO := Order(S, [A!L[i] : i in [1 .. Nrows(L)]]);
        if assigned O`ChangeRingMap then
          LO`ChangeRingMap := O`ChangeRingMap;
        end if;

        I := ideal<LO | P*L^-1>;
// These are suborders, not necessarily the full left and right orders
//        I`LeftOrder := LO;
//        I`RightOrder := LO;
        return I, I;
    else
        LO := Order(S, [A!L[i] : i in [1 .. Nrows(L)]]);
        I := lideal<LO | P*L^-1>;
        RO := Order(S, [A!R[i] : i in [1 .. Nrows(L)]]);
        J := rideal<RO | P*R^-1>;

        if assigned O`ChangeRingMap then
          LO`ChangeRingMap := O`ChangeRingMap;
          RO`ChangeRingMap := O`ChangeRingMap;
        end if;

// These are suborders, not necessarily the full left and right orders
//         I`LeftOrder := LO;
//         J`RightOrder := RO;
        return I, J;
    end if;
end intrinsic;

intrinsic LeftOrder(I::AlgAssVOrdIdl) -> AlgAssVOrd
{The left multiplicator order of I}
    if assigned I`LeftOrder then
        return I`LeftOrder;
    end if;
    /*
    This version has denominator problems as is so just use the old one
    */
    O:= Order(I);
    A := Algebra(O);
    M := BasisMatrix(I)*BasisMatrix(O);
    LL := ColonInternalZ(M, M, A, true);
    L := Order(CoefficientRing(O), [A!LL[i] : i in [1 .. Nrows(LL)]]);

    if assigned O`ChangeRingMap then
      L`ChangeRingMap := O`ChangeRingMap;
    end if;

    if L eq O then
        I`LeftOrder := O;
        return O;
    else
        I`LeftOrder := L;
        return L;
    end if;
end intrinsic;

intrinsic RightOrder(I::AlgAssVOrdIdl) -> AlgAssVOrd
{The right multiplicator order of I}
    if assigned I`RightOrder then
        return I`RightOrder; 
    end if;
    /*  
    This version has denominator problems as is so just use the old one
    */
    O := Order(I);
    A := Algebra(O);
    M := BasisMatrix(I)*BasisMatrix(O);
    RR := ColonInternalZ(M, M, A, false);
    R := Order(CoefficientRing(O), [A!RR[i] : i in [1 .. Nrows(RR)]]);

    if assigned O`ChangeRingMap then
      R`ChangeRingMap := O`ChangeRingMap;
    end if;

    if R eq O then
        I`RightOrder := O;
        return O;
    else
        I`RightOrder := R;
        return R;
    end if;
end intrinsic;

