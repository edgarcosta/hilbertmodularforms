/////////////////////////////////////////////////////////////////////////

/////  Construction of Generators and relations using our program ///////

/////////////////////////////////////////////////////////////////////////
load "config.m";
QQ := Rationals();
M := QuadSpace(5,100);
G,R,Q := ConstructGeneratorsAndRelations(M,2,20);
G1,R1,Q1 := ConstructGeneratorsAndRelationsV2(M,G,R,40);
S := MakeScheme(G1,R1);
P_wtd<X2, X6, X10, X20> := Ambient(S);
eqns_S := DefiningEquations(S);

//// G1 is now an Associtive array with HMF-generators in weights [2,6,10,20]





///////////////////////////////////////////////////////////////////////

///// Construction of Generators and Relations From Hirzebruch  ///////

///////////////////////////////////////////////////////////////////////

// Basis
B1 := Basis(M,[2,2]);
B3 := Basis(M,[6,6]);
B5 := Basis(M,[10,10]);
B15 := Basis(M,[15,15]);
B20 := Basis(M,[20,20]);


// Generators in weights 2,6,10,20
sig1 := B1[1];
sig3 := -2^7*B3[2];
sig5 := 2^12*(-17/145620*B5[2] + 1/1456200*B5[3]);
delta := -115240146944/415277590078125*B20[3] - 512/3737498310703125*B20[4];


//Hirzebruch's Relation
delta^2 eq sig5*(3125*sig5^3 + 2000*sig5^2*sig3*sig1^2 + 256*sig5^2*sig1^5-900*sig5*sig3^3*sig1 -128*sig5*sig3^2*sig1^4 +16*sig3^4*sig1^3 +108*sig3^5);




/////////////////////////////////////////////////////////////////////

/////////////////////////////  Comparison  //////////////////////////

/////////////////////////////////////////////////////////////////////


//Hirzebruchs Scheme
R<w,x,y,z> := PolynomialRing(Rationals(),[2,6,10,20]);
PS := ProjectiveSpace(R);
P := z^2 -y*(3125*y^3 + 2000*y^2*x*w^2 + 256*y^2*w^5 - 900*y*x^3*w - 128*y*x^2*w^4 + 16*x^4*w^3 + 108*x^5);
S := Scheme(PS,P);

//Our Scheme
R1<X2,X6,X10,X20> := PolynomialRing(Rationals(),[2,6,10,20]);
PS1 := ProjectiveSpace(R1);
P1 := -X2^2*X6^6 + 16*X2*X6^3*X20 - 64*X20^2 + 3*X2^3*X6^4*X10 - 864*X6^5*X10 - 16*X2^2*X6*X20*X10 - 3*X2^4*X6^2*X10^2 + 1696*X2*X6^3*X10^2 + 832*X20*X10^2 + X2^5*X10^3 - 896*X2^2*X6*X10^3 + 47296*X10^4;
S1 := Scheme(PS1,P1);



// In this specific case, since we have access to the HMF generating both the rings we can find maps in both direction 


m := map< S -> S1 | [w,(-1/2^7)*x,(1/4096)*y, 1/4194304*w^2*x*y - 1/16777216*w*x^3 - 1/33554432*z + 13/33554432*y^2 ]>;
m1 := map< S1 -> S | [X2,-2^7*X6,4096*X10,-4194304*X2^2*X6*X10 + 4194304*X2*X6^3 - 33554432*X20 + 218103808*X10^2]>;


mm1 := m*m1;
m1m := m1*m; 

DefiningPolynomials(mm1);
DefiningPolynomials(m1m);

//It takes way to long for magma to compute the image of these morphism. Instead do

R2<A2,B6,C10,D20> := PolynomialRing(Rationals(),[2,6,10,20]);
PS2 := ProjectiveSpace(R2);

m2 := map< S -> PS2 | [w,(-1/2^7)*x,(1/4096)*y, 1/4194304*w^2*x*y - 1/16777216*w*x^3 - 1/33554432*z + 13/33554432*y^2 ]>;
m3 := map< S1 -> PS2 | [X2,-2^7*X6,4096*X10,-4194304*X2^2*X6*X10 + 4194304*X2*X6^3 - 33554432*X20 + 218103808*X10^2]>;


DefiningEquation(Image(m2));
DefiningEquation(Image(m3));

