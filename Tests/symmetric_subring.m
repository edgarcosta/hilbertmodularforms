SetNthreads(4);
H<t> := FunctionField(Rationals());

CheckPresentation := procedure(I, tau, weights, series)
    K, images, hs := SymmetricSubringPresentation(I, tau);
    R := Generic(I); P := Generic(K);
    assert Sort(VariableWeights(P)) eq Sort(weights);
    assert H!hs eq series;
    assert H!HilbertSeries(K) eq series;
    assert VerifySymmetricSubringPresentation(I, tau, K, images);
    assert &and[Evaluate(f, images) in I : f in Basis(K)];
    assert &and[Evaluate(f, tau)-f in I : f in images];
end procedure;

R<x,y> := PolynomialRing(Rationals(), [2,2]);
I := ideal<R | >;
CheckPresentation(I, [x,y], [2,2], 1/(1-t^2)^2);
CheckPresentation(ideal<R | y^2-x^2>, [x,-y], [2], 1/(1-t^2));
CheckPresentation(I, [-x,-y], [4,4,4], (1-t^8)/(1-t^4)^3);
P<a,b,c> := PolynomialRing(Rationals(), [4,4,4]);
assert VerifySymmetricSubringPresentation(I, [-x,-y],
    ideal<P | b^2-a*c>, [x^2,x*y,y^2]);
assert not VerifySymmetricSubringPresentation(I, [-x,-y],
    ideal<P | >, [x^2,x*y,y^2]);

R<x,z> := PolynomialRing(Rationals(), [2,4]);
I := ideal<R | >;
CheckPresentation(I, [x,x^2-z], [2,8], 1/((1-t^2)*(1-t^8)));
P<a,b> := PolynomialRing(Rationals(), [2,8]);
assert VerifySymmetricSubringPresentation(I, [x,x^2-z],
    ideal<P | >, [x,(z-x^2/2)^2]);
assert not VerifySymmetricSubringPresentation(I, [x,x^2-z],
    ideal<P | >, [x,z^2]);

R<x,y,z> := PolynomialRing(Rationals(), [2,2,4]);
I := ideal<R | z-x*y>;
CheckPresentation(I, [y,x,x*y], [2,4], 1/((1-t^2)*(1-t^4)));
P<a,b> := PolynomialRing(Rationals(), [2,4]);
assert VerifySymmetricSubringPresentation(I, [y,x,x*y],
    ideal<P | >, [x+y,x*y]);

R<x> := PolynomialRing(Rationals(), [2]);
I := ideal<R | >;
P<a> := PolynomialRing(Rationals(), [4]);
assert not VerifySymmetricSubringPresentation(I, [x], ideal<P | >, [x^2]);
P<a> := PolynomialRing(Rationals(), [2]);
assert not VerifySymmetricSubringPresentation(I, [-x], ideal<P | >, [x]);
assert not VerifySymmetricSubringPresentation(I, [2*x], ideal<P | >, [x]);
for tau in [[2*x]] do
    rejected := false;
    try
        K, images, hs := SymmetricSubringPresentation(I, tau);
    catch e
        rejected := true;
    end try;
    assert rejected;
end for;
R<x,y> := PolynomialRing(Rationals(), [2,2]);
I := ideal<R | x>;
P<a> := PolynomialRing(Rationals(), [2]);
assert not VerifySymmetricSubringPresentation(I, [y,x], ideal<P | >, [y]);
rejected := false;
try
    K, images, hs := SymmetricSubringPresentation(I, [y,x]);
catch e
    rejected := true;
end try;
assert rejected;
print "PASS symmetric subring";
