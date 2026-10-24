// Elkies-Kumar, Algebra & Number Theory 8 (2014), 2297-2411, Section 14.
// On the stored weight-2 chart: a=X2/X1, b=X3/X1^2, t=X7/X1^4.
// The maps identify degree-zero function fields on the stated affine charts.

P<a,b,t>:=PolynomialRing(Rationals(),3);
K:=FieldOfFractions(P);
Q<u,v,z>:=PolynomialRing(Rationals(),3);
L:=FieldOfFractions(Q);
A1 := L!(8*u^2*v^2*(v-4*u)^2);
A := L!(-(9*v^2+72*u*v-54*v+16*u^2-8*u+1)/3);
B1 := L!(-2*v^2*(3*v^4-36*u*v^3+48*u^4*v^2-16*u^3*v^2+148*u^2*v^2-64*u^4*v -224*u^3*v+512*u^5+64*u^4)/3);
B := L!(-2*(108*u^2*v^2-162*u*v^2+405*v^2-648*u^2*v+648*u*v-135*v+64*u^3 -48*u^2+12*u-1)/27);
B2 := L!(-1/2);
f := Q!(-(v^4-6*u*v^3-11*v^3+27*u^4*v^2-18*u^3*v^2+5*u^2*v^2+102*u*v^2-v^2 -288*u^4*v+200*u^3*v-280*u^2*v+8*u*v+1024*u^5-768*u^4+192*u^3 -16*u^2));
IEK := [L|-24*B1/A1,-12*A,96*(A/A1)*B1-36*B,-4*A1*B2];
bad := Q!(u*v*(v - 4*u)*(u-1)*(v-2*u+1)*(v^2+v-2*u)*(v^4-6*u*v^3-11*v^3+27*u^4*v^2-18*u^3*v^2+5*u^2*v^2+102*u*v^2-v^2-288*u^4*v+200*u^3*v-280*u^2*v+8*u*v+1024*u^5-768*u^4+192*u^3-16*u^2));

D0:=a*(a+4*b);
N:=141*a^5*b-a^4*b-286*a^3*b^2+17*a^2*b^2+209*a*b^3-a*b^2-4*b^3;
Z:=D0*t+N/2;
q:=b*(a+4*b)^3/(8*a);
phiFF:=[K|(b-a^2)/(a+4*b),-4*a^2/(a+4*b),Z/q];
branch:=Evaluate(f,[phiFF[1],phiFF[2],K!0])*q^2;
assert Denominator(branch) eq 1;
ai:=v/(4*(4*u-v-1)); bi:=v*(v-4*u)/(16*(4*u-v-1)^2);
ni:=Evaluate(N,[ai,bi,L!0]); qi:=bi*(ai+4*bi)^3/(8*ai);
psiFF:=[L|ai,bi,(qi*z-ni/2)/(ai*(ai+4*bi))];
H:=PolynomialRing(Rationals(),[2,2,4,6,6,6,8]);
rawPullbacks:=[
H.1^2 + 224*H.1*H.2 + 448*H.2^2 + 576*H.3,
H.1^3 - 528*H.1^2*H.2 - 9024*H.1*H.2^2 - 5120*H.2^3 - 1728*H.1*H.3 - 28512*H.2*H.3 - 864*H.5 - 1728*H.6,
1/64*H.1*H.2^4 - 1/32*H.1*H.2^2*H.3 - 1/16*H.2^3*H.3 + 1/64*H.1*H.3^2 + 1/8*H.2*H.3^2 - 1/16*H.3*H.5 - 1/64*H.1^2*H.6,
-15/8*H.2^2*H.3^2 - 61/24*H.3^3 + 1/24*H.2^3*H.4 + 1/24*H.1*H.3*H.4 - 17/24*H.2*H.3*H.4 - 1/24*H.4^2 - 1/12*H.4*H.5 + 5/24*H.5^2 - 1/24*H.2^3*H.6 - 77/24*H.2*H.3*H.6 - 11/24*H.4*H.6 - 43/24*H.5*H.6 - 13/24*H.6^2
];
rawImages:=[H|H.1,H.2,H.3,-H.4+H.2^3-17*H.2*H.3+H.1*H.3+H.5-11*H.6,H.5,H.6,H.7];
pullbacks:=[Evaluate(p,rawImages):p in rawPullbacks];
hashes:=["65a4f3e135362debba00a6a8422327dde0669d3434793cb6324f6278d9c44cdc","08dd896c0524576146cbdeef41f940196f56d8e64ed9caab39a94249c629a40f"];
return <P,K,Q,L,f,Z,P!branch,phiFF,psiFF,pullbacks,hashes,bad,IEK>;
