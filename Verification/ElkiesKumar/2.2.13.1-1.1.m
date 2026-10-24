// Elkies-Kumar, Algebra & Number Theory 8 (2014), 2297-2411, Section 9.
// In van der Geer-Zagier coordinates: a=X6/(X2*X4), b=X4/X2^2, t=X8/X2^4.
// The maps identify the degree-zero function fields; they make no boundary claim.

P<a,b,t> := PolynomialRing(Rationals(),3);
K := FieldOfFractions(P);
Q<g,h,z> := PolynomialRing(Rationals(),3);
L := FieldOfFractions(Q);
f := Q!(-128*g^3 - 27*g^2*h^2 + 656*g^2*h + 192*g^2 + 108*g*h^3 - 468*g*h^2 + 568*g*h - 96*g + 4*h^2 - 16*h + 16);
Z := a*t;
q := b^2*(4*a-b)/(8*a);
phiFF := [K|(b-4*a)/(2*b),-4*a^2/(4*a-b),Z/q];
branch := Evaluate(f,[phiFF[1],phiFF[2],K!0])*q^2;
assert Denominator(branch) eq 1;
ai := -2*g*h/(2*g-1);
bi := 8*g*h/(2*g-1)^2;
qi := bi^2*(4*ai-bi)/(8*ai);
psiFF := [L|ai,bi,qi*z/ai];
H := PolynomialRing(Rationals(),[2,4,6,6,8]);
pullbacks := [H|H.1^2+192*H.2,H.1^3-576*H.1*H.2-864*H.3-864*H.4,H.1*H.2^2/64-H.2*H.3/16-H.1^2*H.4/64+H.2*H.4/16,H.1^2*H.2^2/96-H.1*H.2*H.3/24+H.3^2/4-H.1^3*H.4/96+H.1*H.2*H.4/24+H.3*H.4/2+H.4^2/4];
hashes := ["65a4f3e135362debba00a6a8422327dde0669d3434793cb6324f6278d9c44cdc","7ac64786a8078e39e8207a9a7b046c4e365cf7dfd8fc17691ce175fb62cabf87"];
excludedEK := Q!(-32768*g^13*h - 170752*g^12*h^3 + 184320*g^12*h^2 + 204800*g^12*h + 1145088*g^11*h^5 + 1804672*g^11*h^4 + 402496*g^11*h^3 - 541696*g^11*h^2 - 536576*g^11*h + 248832*g^10*h^7 - 6300288*g^10*h^6 - 7246848*g^10*h^5 - 3092384*g^10*h^4 - 325760*g^10*h^3 + 91648*g^10*h^2 + 786432*g^10*h - 1119744*g^9*h^8 + 5927040*g^9*h^7 + 642112*g^9*h^6 + 521648*g^9*h^5 - 1089984*g^9*h^4 - 864208*g^9*h^3 + 1254144*g^9*h^2 - 712704*g^9*h + 373248*g^8*h^9 + 1253376*g^8*h^8 - 3222016*g^8*h^7 + 1211672*g^8*h^6 + 4111104*g^8*h^5 - 1295120*g^8*h^4 + 2882416*g^8*h^3 - 1882752*g^8*h^2 + 408576*g^8*h + 497664*g^7*h^10 - 3227904*g^7*h^9 + 8583072*g^7*h^8 - 7499480*g^7*h^7 + 4364584*g^7*h^6 - 6766388*g^7*h^5 + 5915496*g^7*h^4 - 3271780*g^7*h^3 + 1234752*g^7*h^2 - 139776*g^7*h + 82944*g^6*h^10 + 190368*g^6*h^9 - 3121520*g^6*h^8 + 9043968*g^6*h^7 - 8383284*g^6*h^6 + 5422572*g^6*h^5 - 4053786*g^6*h^4 + 1698256*g^6*h^3 - 385248*g^6*h^2 + 19968*g^6*h - 10368*g^5*h^10 + 198336*g^5*h^9 - 550080*g^5*h^8 - 295704*g^5*h^7 + 2615360*g^5*h^6 - 2040056*g^5*h^5 + 937052*g^5*h^4 - 326155*g^5*h^3 + 24336*g^5*h^2 + 4224*g^5*h - 14208*g^4*h^9 + 159456*g^4*h^8 - 504056*g^4*h^7 + 514304*g^4*h^6 - 4808*g^4*h^5 + 35370*g^4*h^4 - 46526*g^4*h^3 + 20088*g^4*h^2 - 2528*g^4*h - 6560*g^3*h^8 + 54144*g^3*h^7 - 152968*g^3*h^6 + 170776*g^3*h^5 - 69546*g^3*h^4 + 29212*g^3*h^3 - 6144*g^3*h^2 + 464*g^3*h - 1088*g^2*h^7 + 7200*g^2*h^6 - 16760*g^2*h^5 + 15392*g^2*h^4 - 4312*g^2*h^3 + 704*g^2*h^2 - 32*g^2*h - 32*g*h^6 + 192*g*h^5 - 392*g*h^4 + 288*g*h^3 - 32*g*h^2);
IEK := [L|32*g + 24*h^2 - 48*h + 8,16*g^2 - 192*g*h - 16*g + 4,192*g^3 + 416*g^2*h^2 - 1824*g^2*h - 160*g^2 - 1536*g*h^3 + 2944*g*h^2 - 640*g*h + 16*g + 32*h^2 - 64*h + 8,64*g^4*h^2];
// Rings and fields, radicands, rational maps, Siegel pullbacks, source SHA256s,
// excluded EK locus, and the published Igusa-Clebsch tuple, in that order.
return <P,K,Q,L,f,Z,P!branch,phiFF,psiFF,pullbacks,hashes,excludedEK,IEK>;
