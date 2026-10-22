// Replay the abstract presentation in Hermann's Satz 6 inside the stored ring.
// The recorded geometric swap was recovered at separating precision 200.
// The normalized theta dictionary remains pending.
SetNthreads(4);
datafile := "Verification/LiteratureEquations/2.2.17.1-1.1-HermannSymmetric.m";
SymmetricLitData := eval(Read(datafile) cat "return SymmetricLitData;");
HermannAbstractInclusion := eval(Read(datafile) cat "return HermannAbstractInclusion;");
I,citation := SymmetricLitData();
assert IsHomogeneous(I);
assert Sort([WeightedDegree(f) : f in Basis(I)]) eq [10,12,12];
J := LoadStoredCanonicalRing("2.2.17.1-1.1"); R := Generic(J);
inclusion,tau := HermannAbstractInclusion(R);
assert VerifySymmetricSubringPresentation(J,tau,I,inclusion);
K,ki,hs := SymmetricSubringPresentation(J,tau);
assert VariableWeights(Generic(K)) eq [2,4,4,6,6];
assert HilbertSeries(I) eq HilbertSeries(K);
H<t> := FunctionField(Rationals());
assert H!hs eq (1-t^10-2*t^12+t^16+t^18)/((1-t^2)*(1-t^4)^2*(1-t^6)^2);
printf "Hermann D17: exact abstract kernel and invariant image, weights %o.\n", VariableWeights(Generic(K));
print "PASS Hermann D17 abstract presentation; normalized theta dictionary pending";
