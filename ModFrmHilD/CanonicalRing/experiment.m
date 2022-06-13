// Random file for Hilbert Series investigations.

function EvenCoefficients(X)
    coeffs := Coefficients(X);
    return coeffs[1..#coeffs by 2];
end function;

function by2(X)
    return X[1..#X by 2];
end function;

function by3(X)
    return X[1..#X by 3];
end function;

function by6(X)
    return X[1..#X by 6];
end function;


for D in [2..50] do

    if not IsSquarefree(D) then continue; end if;
    K := QuadraticField(D);
    if Discriminant(K) gt 42 then continue; end if;

    print "Discriminant:", Discriminant(K);

    PP<T> := PowerSeriesRing(Rationals(), 100);

    G := CongruenceSubgroup(K);
    g, hilb, hilbI, Q, poly := GeneratorWeightBound(G : experiment:=true);

    print "den: ", Denominator(poly);
    
    S<t> := Parent(hilb); 
    //hilbI3 := t^6 * hilb;
    //Q := t^6 * 3*g/(1-t^2)^2 + 1;

    
    coeffsQ := EvenCoefficients(PP ! Q);
    floorQ := [Floor(x) : x in EvenCoefficients(PP ! Q)];
    diffy  := [(x) : x in EvenCoefficients(PP ! (hilb-hilbI))];

    print "m * c1(Kappa(log D)):", g;
    print [diffy[i] - floorQ[i] : i in [2..#diffy by 1]];
    //print Maximum([Abs(floorQ[i] - diffy[i]) : i in [20..#floorQ]]);
    print "";
    print diffy;
    print coeffsQ;
    print "";
    
    //print Matrix([by3(diffy), by3(floorQ)]);
    //print "";
    //print coeffsQ;
    
end for;

