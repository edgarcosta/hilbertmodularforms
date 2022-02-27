
// Make sure to attach the spec file.

function EvenCoefficients(X)
    coeffs := Coefficients(X);
    return coeffs[1..#coeffs by 2];
end function;

for D in [2..50] do

    if not IsSquarefree(D) then continue; end if;
    K := QuadraticField(D);
    if Discriminant(K) gt 42 then continue; end if;

    print "Discriminant:", D;

    PP<T> := PowerSeriesRing(Rationals(), 100);

    G := CongruenceSubgroup(K);
    g, hilb, hilbI, Q := WrongGeneratorWeightBound(G);

    floorQ := [Floor(x) : x in EvenCoefficients(PP ! Q)];
    diffy  := EvenCoefficients(PP ! (hilb-hilbI));

    print "c1(Kappa(log D)):", g;
    print floorQ;
    print diffy;
    print Maximum([Abs(floorQ[i] - diffy[i]) : i in [20..#floorQ]]);
    print "";
end for;

// Added a pointless comment.
