// Elkies-Kumar, Algebra & Number Theory 8 (2014), 2297-2411, Section 6.
// On the X2 chart: a=X6/X2^3, b=X10/X2^5, t=X20/X2^10.
// The maps identify the degree-zero function fields; they make no boundary claim.

P<a,b,t> := PolynomialRing(Rationals(),3);
K := FieldOfFractions(P);
Q<g,h,z> := PolynomialRing(Rationals(),3);
L := FieldOfFractions(Q);
f := Q!(2*(6250*h^2-4500*g^2*h-1350*g*h-108*h-972*g^5-324*g^4-27*g^3));
Z := 2^22*(a^3-a*b-8*t+52*b^2);
branch := Evaluate(f,[K|-b/(6*a^2),b^3/a^5,0])*(2^23*a^5/b)^2;
assert Denominator(branch) eq 1;
phiFF := [K|-b/(6*a^2), b^3/a^5, Z*b/(2^23*a^5)];
ai := -h/(216*g^3);
bi := -h^2/(7776*g^5);
psiFF := [L|ai,bi,(ai^3-ai*bi+52*bi^2-2*ai^5*z/bi)/8];
H := PolynomialRing(Rationals(),[2,6,10,20]);
pullbacks := [H|H.1^2,H.1^3-864*H.2,-H.3/4,H.2^2/4-H.1*H.3/6];
hashes := ["65a4f3e135362debba00a6a8422327dde0669d3434793cb6324f6278d9c44cdc",
"0b7a1f389362e8f38e9b2be689be1c6e558ef0c4694d021ca986cf97e9c1f0dc"];
excludedEK := Q!(h*(8*h-9*g^2)*(64*h^2+48*g^2*h+48*g^5+9*g^4)*(6250*h^2-4500*g^2*h-1350*g*h-108*h-972*g^5-324*g^4-27*g^3));
IEK := [L|-24*(-(g+1/4))/(1),-12*(-3*g^2/4),96*((-3*g^2/4)/(1))*(-(g+1/4))-36*(-(g^3/4 + h)),-4*(1)*(-h^2)];
// Rings and fields, radicands, rational maps, Siegel pullbacks, source SHA256s,
// excluded EK locus, and the published Igusa-Clebsch tuple, in that order.
return <P,K,Q,L,f,Z,P!branch,phiFF,psiFF,pullbacks,hashes,excludedEK,IEK>;
