// Elkies-Kumar, Algebra & Number Theory 8 (2014), Section 10.
// On X1=1, a=X2/X3, b=X5/X3 and t=X4 in the stored coordinates.
// Every denominator and both source bad loci are excluded from this chart.
P<a,b,t>:=PolynomialRing(Rationals(),3); K:=FieldOfFractions(P);
Q<u,v,z>:=PolynomialRing(Rationals(),3); L:=FieldOfFractions(Q);
A1 := L!((2*u+1)^2);
A := L!(-(16*v^2-8*u^2*v+20*u*v+64*v+u^4+4*u^3+6*u^2+4*u+1)/3);
B1 := L!(-(48*v^2-16*u^2*v-40*u*v-16*v+4*u^4-12*u^3-23*u^2-12*u-2)/3);
B := L!(-2*(64*v^3-48*u^2*v^2-312*u*v^2+978*v^2+12*u^4*v-6*u^3*v+72*u^2*v+210*u*v +120*v-u^6-6*u^5-15*u^4-20*u^3-15*u^2-6*u-1)/27);
B2 := L!(-64*v^3);
f := Q!(-(256*v^3-192*u^2*v^2-464*u*v^2-185*v^2+48*u^4*v-236*u^3*v-346*u^2*v -144*u*v-18*v-4*u^6-20*u^5-41*u^4-44*u^3-26*u^2-8*u-1));
IEK := [L|-24*B1/A1,-12*A,96*(A/A1)*B1-36*B,-4*A1*B2];
bad := Q!(v*(2*u+1)*(v-u^2-2*u-1)*(256*v^3-192*u^2*v^2-464*u*v^2-185*v^2+48*u^4*v-236*u^3*v-346*u^2*v-144*u*v-18*v-4*u^6-20*u^5-41*u^4-44*u^3-26*u^2-8*u-1));

Z:=t-a*b*(4*b+1)*(a*b+4*b+1)/(2*(a-1)^2);
q:=2*a^4*b*(4*b+1)^2/(a-1)^4;
phiFF:=[K|-(a+1)/(2*a),b*(a-1)^2/(4*a^2*(4*b+1)),Z/q];
B:=Evaluate(f,[phiFF[1],phiFF[2],K!0])*q^2;
ai:=-1/(2*u+1); bi:=v/((u+1)^2-4*v);
qi:=2*ai^4*bi*(4*bi+1)^2/(ai-1)^4;
psiFF:=[L|ai,bi,qi*z+ai*bi*(4*bi+1)*(ai*bi+4*bi+1)/(2*(ai-1)^2)];
H:=PolynomialRing(Rationals(),[2,4,4,6,6,6,8]);
rawPullbacks:=[H|H.1^2 + 216*H.2 - 72*H.3,
H.1^3 - 540*H.1*H.2 - 108*H.1*H.3 - 864*H.5 - 6696*H.6,
-1/4*H.3*H.5,
1/16*H.1*H.3*H.4 - 1/16*H.4^2 - 245/48*H.1*H.3*H.5 + 21/4*H.4*H.5 - 10*H.5^2 - 31/16*H.4*H.6 - 41/8*H.5*H.6 - 2*H.2*H.7 + 5*H.3*H.7];
rawImages:=[H|H.1,H.2,H.3,H.4,H.5,H.6,H.7-2*H.3^2];
pullbacks:=[Evaluate(p,rawImages):p in rawPullbacks];
hashes:=["65a4f3e135362debba00a6a8422327dde0669d3434793cb6324f6278d9c44cdc","89141902b5511e95a7bb5bb36b54a720e9f92d126029b8a0413b456aa980759e"];
return <P,K,Q,L,f,Z,B,phiFF,psiFF,pullbacks,hashes,bad,IEK>;
