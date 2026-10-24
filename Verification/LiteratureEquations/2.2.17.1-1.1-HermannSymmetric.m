// C. F. Hermann, Math. Ann. 256 (1981), pp.191-197, Satz 5 and Satz 6.
// Variables are [G2, G4, H4, G6, H6]; the three relations are printed on p.196.
// The abstract inclusion below does not identify normalized theta expansions.
SymmetricLitData := function()
    S<G2,G4,H4,G6,H6> := PolynomialRing(Rationals(), [2,4,4,6,6]);
    I := ideal<S | G4*G6-H4*H6,
        G4^3-G6*H6/4+G4*G6*G2/4,
        G6^2-4*H4*G4^2-G6*H4*G2>;
    citation := "Hermann (1981), Satz 5 and Satz 6, pp.195-196";
    return I, citation;
end function;

// R is the stored full-ring ambient ring, with weights [2, 4, 4, 6, 6, 6, 8].
// The involution is the geometric swap, transported from separating q-expansions.
HermannAbstractInclusion := function(R)
    assert VariableWeights(R) eq [2,4,4,6,6,6,8];
    x := [R.i : i in [1..7]];
    inclusion := [-16*x[1], -16*x[2]+16*x[3], x[2],
        64*x[6], 1024*x[5]-1024*x[6]];
    tau := [x[1],x[2],x[3],x[1]*x[3]-x[4]+4*x[5]+x[6],x[5],x[6],
        -x[2]^2/4-3*x[2]*x[3]/2+15*x[3]^2/4+x[1]*x[5]+x[1]*x[6]/4-x[7]];
    return inclusion, tau;
end function;
