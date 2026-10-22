// Hammond, American Journal of Mathematics 88 (1966), 497-516:
// pp. 507-508 for D=5 and Theorem 6.2, p. 514, for D=8.

// These are polynomial presentations of the even, symmetric, trivial-character
// level-one rings for SL_2(O), with actual parallel weights as degrees.
// Symmetric means f(z2,z1)=f(z1,z2), without a weight sign (Definition 1.2, p. 499).

// Hammond uses Siegel restriction: h2, G6*, (theta^2)* for D=5, and
// h2, (theta_2*)^2, G6* for D=8, ordered here by weight. The last theta
// expression in each field generates the ideal of diagonal-vanishing forms.
// His diagonal normalizations are h2*=g4 and (G6*)*=g6^2 (p. 507).

// The maps below match abstract graded generators over Q. They do not identify
// Hammond's normalized Siegel restrictions or their diagonal values.
// The stored coordinates and their geometric swap are transported through the
// existing Hirzebruch full-ring witnesses in the accompanying example.
SymmetricLitData := function()
    P5<h2,h6,h10> := PolynomialRing(Rationals(), [2,6,10]);
    P8<k2,k4,k6> := PolynomialRing(Rationals(), [2,4,6]);
    sources := [* ideal<P5 | >, ideal<P8 | > *];
    J5 := LoadStoredCanonicalRing("2.2.5.1-1.1"); R5 := Generic(J5);
    J8 := LoadStoredCanonicalRing("2.2.8.1-1.1"); R8 := Generic(J8);
    assert VariableWeights(R5) eq [2,6,10,20];
    assert VariableWeights(R8) eq [2,4,6,14];
    maps := [* hom<P5 -> R5 | [R5.1,R5.2,R5.3]>,
        hom<P8 -> R8 | [R8.1,R8.2,R8.3]> *];
    citation := "Hammond, Amer. J. Math. 88 (1966), pp. 507-508 and Theorem 6.2, p. 514";
    return sources, [* J5,J8 *], maps, citation;
end function;
return SymmetricLitData;
