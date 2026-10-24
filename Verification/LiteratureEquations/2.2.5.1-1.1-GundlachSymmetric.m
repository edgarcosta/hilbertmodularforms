// Gundlach, Math. Ann. 152 (1963), Satz 5-6, p.241: symmetric even forms
// for SL2(O_Q(sqrt5)). Positive weights replace his negative dimensions.
// This rational presentation and its stored inclusion are abstract; they do
// not identify the source's normalized G_{-2}, G_{-6}, or Theta^2.
SymmetricLitData := function()
    P<a2,a6,a10> := PolynomialRing(Rationals(), [2,6,10]);
    I := ideal<P | >;
    R<x2,x6,x10,x20> := PolynomialRing(Rationals(), [2,6,10,20]);
    images := [R | x2,x6,x10];
    citation := "Gundlach, Math. Ann. 152 (1963), 226-256, Satz 5-6, p.241 (abstract graded presentation over Q)";
    return I, citation, images;
end function;
return SymmetricLitData;
