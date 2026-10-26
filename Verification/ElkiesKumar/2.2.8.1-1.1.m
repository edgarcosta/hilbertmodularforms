// Elkies-Kumar, Algebra & Number Theory 8 (2014), 2297-2411, Section 7.
// On the X2 chart: a=X4/X2^2, b=X6/X2^3, t=X14/X2^7.
// The maps identify the degree-zero function fields; they make no boundary claim.

P<a,b,t> := PolynomialRing(Rationals(),3);
K := FieldOfFractions(P);
Q<r,s,z> := PolynomialRing(Rationals(),3);
L := FieldOfFractions(Q);
f := Q!(32*r^3 + 64*r^2*s + 48*r^2 + 32*r*s^2 - 80*r*s + 24*r - 2*s + 4);
Z := -2*t+2*a^3+a*b+20*a^2*b+2*b^2;
q := b*(a+4*b)^2/(2*a);
branch := Evaluate(f,[K|-2*b/(a+4*b),-8*a^3/(b*(a+4*b)),0])*q^2;
assert Denominator(branch) eq 1;
phiFF := [K|-2*b/(a+4*b),-8*a^3/(b*(a+4*b)),Z/q];
ai := r*s/(16*(2*r+1)^2);
bi := -r^2*s/(32*(2*r+1)^3);
qi := bi*(ai+4*bi)^2/(2*ai);
psiFF := [L|ai,bi,(2*ai^3+ai*bi+20*ai^2*bi+2*bi^2-qi*z)/2];
H := PolynomialRing(Rationals(),[2,4,6,14]);
pullbacks := [H|H.1^2+144*H.2,H.1^3-648*H.1*H.2-1728*H.3,-H.2*H.3/4,H.2^3+H.1*H.2*H.3/12+H.3^2];
hashes := [ "65a4f3e135362debba00a6a8422327dde0669d3434793cb6324f6278d9c44cdc", "58707dbad72f895da9286a06817ddd43c97d4f147e9d184044c1c30b96a568e7" ];
excludedEK := Q!(256*r^7*s + 1088*r^6*s^2 + 1152*r^6*s + 1840*r^5*s^3 + 2048*r^5*s^2 + 2112*r^5*s + 1440*r^4*s^4 + 552*r^4*s^3 - 688*r^4*s^2 + 2016*r^4*s + 432*r^3*s^5 - 792*r^3*s^4 - 1968*r^3*s^3 - 2896*r^3*s^2 + 1056*r^3*s - 1179*r^2*s^4 + 3172*r^2*s^3 - 1516*r^2*s^2 + 288*r^2*s + 72*r*s^3 - 160*r*s^2 + 32*r*s);
IEK := [L|-32*r - 12*s + 8,16*r^2 + 36*r*s + 16*r + 4,-192*r^3 - 376*r^2*s - 160*r^2 - 144*r*s^2 + 140*r*s - 16*r - 16*s + 8,-8*r^3*s^2];
// Rings and fields, radicands, rational maps, Siegel pullbacks, source SHA256s,
// excluded EK locus, and the published Igusa-Clebsch tuple, in that order.
return <P,K,Q,L,f,Z,P!branch,phiFF,psiFF,pullbacks,hashes,excludedEK,IEK>;
