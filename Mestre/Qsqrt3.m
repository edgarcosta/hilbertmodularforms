function IgusaClebschInvariants_Sqrt3()
    // The graded ring of modular forms for GL(Z[sqrt(3)])
    MGL<X2,X4,X6> := PolynomialRing(Rationals(), [2,4,6]);
    // The graded ring for modular forms for SL(Z[sqrt(3)]) is
    // the double cover , which we define as a quotient 
    // of this polynomial ring (Y4 = sqrt(2 X2 X6))
    Mbig<X2,X4,X6,Y4> := PolynomialRing(Rationals(), [2,4,6,4]);
    MSL<X2,X4,X6,Y4> := quo<Mbig | Y4^2 - 2*X2*X6>;
    // These are the pullbacks of Igusa's generators
    psi_4_plus := 1/4*X2^2 + 72*X4;
    psi_6_plus := 1/8*X2^3 - 162*X2*X4 - 1728*X6;
    chi_10_plus := 1/8*X4*X6;
    chi_12_plus := 1/8*X4^3 - 1/24*X2*X4*X6 + X6^2;
    psi_4_minus := 60*Y4;
    psi_6_minus := -63*X2*Y4;
    chi_10_minus := 1/16*X6*Y4;
    chi_12_minus := -1/16*X4^2*Y4 + 1/48*X2*X6*Y4;
    assert psi_4_minus^2 eq 7200*X2*X6;
    assert psi_4_minus * psi_6_minus eq -7560*X2^2*X6;
    assert psi_4_minus * chi_10_minus eq 15/2*X2*X6^2;
    assert  psi_4_minus * chi_12_minus eq -15/2*X2*X4^2*X6 + 5/2*X2^2*X6^2;
    psi_4 := psi_4_plus + psi_4_minus;
    psi_6 := psi_6_plus + psi_6_minus;
    chi_10 := chi_10_plus + chi_10_minus;
    chi_12 := chi_12_plus + chi_12_minus;
    // Renaming the variables the same way in the function field
    _<X2, X4, X6, Y4> := chi_12/chi_10; 
    // Igusa-Clebsch invariants
    I2 := -24*chi_12/chi_10;
    I4 := 4*psi_4;
    I6 := -8/3*psi_6-32*psi_4*chi_12/chi_10;
    I10 := -2^14*chi_10;
    ICInv := [I2, I4, I6, I10];
    return ICInv;
end function;

// Copied from Magma's package code
// Following Mestre's construction of he conic and the cubic
function ConicLAndCubicM(ICInv)
    AP, BP, CP, DP := Explode(ICInv);
    // Inv := IgusaClebschToClebsch(ICInv);
    A :=-AP/120 ;
    B :=(BP+720*A^2)/6750 ;
    C :=(CP-8640*A^3+108000*A*B)/202500 ;
    D :=(DP+62208*A^5-972000*A^3*B-1620000*A^2*C
        +3037500*A*B^2+6075000*B*C)/(-4556250) ;
    // A, B, C, D := Explode(Inv);
    U := A^6;
    K := Parent(A);
    A11 := 2*C+A*B/3 ;
    A22 := D;
    A33 := B*D/2+2*C*(B^2+A*C)/9 ;
    A23 := B*(B^2+A*C)/3+C*(2*C+A*B/3)/3 ;
    A31 := D;
    A12 := 2*(B^2+A*C)/3 ;
    A32 := A23;  A13 := A31;  A21 := A12;
    C11 := A11*U^2*DP^8/DP^11 ;
    C22 := A22*DP^10/DP^11 ;
    C33 := A33*U^8/DP^11 ;
    C23 := A23*DP^5*U^4/DP^11 ;
    C31 := A31*DP^4*U^5/DP^11 ;
    C12 := A12*U*DP^9/DP^11 ;
    C32 := C23;  C13 := C31;  C21 := C12;
    a111 := 8*(A^2*C-6*B*C+9*D)/36 ;
    a112 := 4*(2*B^3+4*A*B*C+12*C^2+3*A*D)/36 ;
    a113 := 4*(A*B^3+4*A^2*B*C/3+4*B^2*C+6*A*C^2+3*B*D)/36 ;
    a122 := a113;
    a123 := 2*(2*B^4+4*A*B^2*C+4*A^2*C^2/3+4*B*C^2+3*A*B*D+12*C*D)/36 ;
    a133 := 2*(A*B^4+4*A^2*B^2*C/3+16*B^3*C/3+26*A*B*C^2/3+
            8*C^3+3*B^2*D+2*A*C*D)/36 ;
    a222 := 4*(3*B^4+6*A*B^2*C+8*A^2*C^2/3+2*B*C^2-3*C*D)/36 ;
    a223 := 2*(-2*B^3*C/3-4*A*B*C^2/3-4*C^3+9*B^2*D+8*A*C*D)/36 ;
    a233 := 2*(B^5+2*A*B^3*C+8*A^2*B*C^2/9+2*B^2*C^2/3
            -B*C*D+9*D^2)/36 ;
    a333 := 1*(-2*B^4*C-4*A*B^2*C^2-16*A^2*C^3/9-4*B*C^3/3
            +9*B^3*D+12*A*B*C*D+20*C^2*D)/36 ;
    P := U^(-18)*DP^5 ;
    c111 := a111*P*U^3*DP^12 ;
    c112 := a112*P*U^2*DP^13 ;
    c113 := a113*P*U^6*DP^8 ;
    c122 := a122*P*U*DP^14 ;
    c123 := a123*P*U^5*DP^9 ;
    c133 := a133*P*U^9*DP^4 ;
    c222 := a222*P*DP^15 ;
    c223 := a223*P*U^4*DP^10 ;
    c233 := a233*P*U^8*DP^5 ;
    c333 := a333*P*U^12 ;
    PP<Z1,Z2,Z3> := PolynomialRing(K,3);
    L := C11*Z1^2+C22*Z2^2+C33*Z3^2+2*C12*Z1*Z2+2*C13*Z1*Z3+2*C23*Z2*Z3;
    M := c111*Z1^3+c222*Z2^3+c333*Z3^3+3*c112*Z1^2*Z2+3*c113*Z1^2*Z3+3*c122*Z1*Z2^2+3*c133*Z1*Z3^2+3*c233*Z2*Z3^2+3*c223*Z2^2*Z3+6*c123*Z1*Z2*Z3;
    return [L,M];
end function;

procedure code_that_ran()
    I2_chi10 := -24*chi_12;
    I4_chi10_2 := 4*psi_4*chi_10^2;  
    I6_chi10_3 := (-8/3*psi_6*chi_10-32*psi_4*chi_12)*chi_10^2;
    I10_chi10_5 := -2^14*chi_10^6;  
    A :=-AP/120 ;
    B :=(BP+720*A^2)/6750 ;
    C :=(CP-8640*A^3+108000*A*B)/202500 ;
    D :=(DP+62208*A^5-972000*A^3*B-1620000*A^2*C
        +3037500*A*B^2+6075000*B*C)/(-4556250) ;
Type(A);
Type(B);
Type(C);
A;
B;
C;
D;
U := A^6;
 K := Parent(A);
A11 := 2*C+A*B/3 ;
    A22 := D;
    A33 := B*D/2+2*C*(B^2+A*C)/9 ;
    A23 := B*(B^2+A*C)/3+C*(2*C+A*B/3)/3 ;
    A31 := D;
    A12 := 2*(B^2+A*C)/3 ;
    A32 := A23;  A13 := A31;  A21 := A12;
C11 := A11*U^2*DP^8;
C22 := A22*DP^10;
C33 := A33*U^8;
 C23 := A23*DP^5*U^4;
C31 := A31*DP^4*U^5;
C12 := A12*U*DP^9;
C32 := C23;  C13 := C31;  C21 := C12;
 PP<Z1,Z2,Z3> := PolynomialRing(K,3);
L := C11*Z1^2+C22*Z2^2+C33*Z3^2+2*C12*Z1*Z2+2*C13*Z1*Z3+2*C23*Z2*Z3;
end procedure;

// From the Cowan-Frengley-Kimball paper, this is the form Q3
// with Gram Matrix T3
function RMSimplifiedMestreConic(A,A1,B,B1,B2)
        T11 := -225A1^3*B + 285*A*A1^2*B1 + 324*B1^3;
        T12 := 20*A^2*A1^2 - 45*A1*B*B1 + 36*A*B1^2;
        T13 := 90*A*A1^2*B + 30*A^2*A1*B1 - 375*A1^3*B2 + 162*B*B1^2;
        T22 := -60*A*A1*B + 4*A^2*B1 + 125*A1^2*B2;
        T23 := 20*A^3*A1 - 135*A1*B^2 + 18*A*B*B1 + 450*A1*B1*B2;
        T33 := 180*A^2*A1*B - 525*A*A1^2*B2 + 81*B^2*B1;
        
end function;
