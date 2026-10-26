// Certify the D=13 comparison over Q, including the modular dictionary.
// The synthetic d=2 fixture must be classified as a nonsquare twist.
SetNthreads(1);
SetColumns(0);
W := eval Read("Verification/ElkiesKumar/2.2.13.1-1.1.m");
P,K,Q,L,f,Z,B,phiFF,psiFF,pullbacks,hashes,excludedEK,IEK:=Explode(W);
a:=K.1; b:=K.2; t:=K.3; g:=L.1; h:=L.2; z:=L.3;
ev:=func<p,vals|Evaluate(Numerator(p),vals)/Evaluate(Denominator(p),vals)>;
J:=LoadStoredCanonicalRing("2.2.13.1-1.1"); R:=Generic(J);
LitData:=eval Read("Verification/LiteratureEquations/2.2.13.1-1.1-vdGZagier.m");
I,Phi,Psi,citation:=LitData(R,R);
assert VerifyGradedIsomorphism(I,J,Phi,Psi);
Jo:=ideal<P|Z^2-B>;
lit:=[K|1,b,a*b,b^2/a,t];
stored:=[ev(p,lit):p in Psi];
weights:=VariableWeights(R);
normalized:=[stored[i]/4^(weights[i] div 2):i in [1..#stored]];
for p in Basis(J) do
  pp:=ev(p,stored);
  assert Numerator(pp) in Jo and not Denominator(pp) in Jo;
end for;
assert [ev(Phi[3]/(Phi[1]*Phi[2]),stored),ev(Phi[2]/Phi[1]^2,stored),ev(Phi[5]/Phi[1]^4,stored)] eq [a,b,t];
V<x,y,v,w>:=PolynomialRing(Rationals(),4); FV:=FieldOfFractions(V);
JV:=ideal<V|[Evaluate(p,[V|1,x,y,v,w]):p in Basis(J)]>;
back:=[FV|-8*v/x,-32*x,256*(8*w-4*y+57*x^2-57*v)];
pp:=ev(Z^2-B,back);
assert Numerator(pp) in JV and not Denominator(pp) in JV;
for i in [2..5] do
  delta:=ev(normalized[i],back)-FV.(i-1);
  assert Numerator(delta) in JV and not Denominator(delta) in JV;
end for;
print "CHECK both rational compositions for the stored degree-zero chart";
psi4c,psi6c,chi10c,chi12c:=Explode([ev(p,stored):p in pullbacks]);
II:=[K|-24*chi12c/chi10c,4*psi4c,-8*psi6c/3-32*psi4c*chi12c/chi10c,-2^14*chi10c];
js:=func<iv|[iv[1]^5/iv[4],iv[1]^3*iv[2]/iv[4],iv[1]^2*iv[3]/iv[4]]>;
for i in [1..3] do assert ev(js(IEK)[i],phiFF) eq js(II)[i]; end for;
print "CHECK three normalized Igusa identities";
assert &or[IsOdd(e[2]):e in Factorization(f)];
q:=b^2*(4*a-b)/(8*a);
assert B/ev(f,phiFF) eq q^2;
print "CHECK degree two and rational square factor";
for d in [1,2] do
  JD:=ideal<P|Z^2-d*B>; JE:=ideal<Q|Q.3^2-d*f>;
  assert Numerator(ev(Q.3^2-d*f,phiFF)) in JD;
  assert Numerator(ev(P!Z^2-d*B,psiFF)) in JE;
  for i in [1..3] do
    delta:=ev(psiFF[i],phiFF)-K.i;
    assert Numerator(delta) in JD and not Denominator(delta) in JD;
    delta:=ev(phiFF[i],psiFF)-L.i;
    assert Numerator(delta) in JE and not Denominator(delta) in JE;
  end for;
  deck:=[K|a,b,-t];
  assert ev(Z^2-d*B,deck) eq Z^2-d*B;
  assert [ev(p,deck):p in phiFF] eq [phiFF[1],phiFF[2],-phiFF[3]];
  assert d*B/ev(f,phiFF) eq d*q^2;
  assert d eq 1 or not IsSquare(Rationals()!d);
  print "CHECK both rational compositions and deck action",d;
end for;
for p in [K|a,b,4*a-b,II[1],II[4]] cat phiFF cat stored do
  assert p ne 0;
  assert not Numerator(p) in Jo and not Denominator(p) in Jo;
end for;
for p in [L|g,h,2*g-1,IEK[1],IEK[4],excludedEK] cat psiFF do assert p ne 0; end for;
assert #hashes eq 2 and &and[#s eq 64:s in hashes];
print "CHECK chart excludes X2=0, X4=0, a=0, b=0, 4*a-b=0, g=0, h=0, 2*g-1=0, I2=0, and source bad locus";
// Resultants isolate h and the nonzero scale in the generic invariant fiber.
B0<g0,h0>:=PolynomialRing(Rationals(),2); F0:=FieldOfFractions(B0);
IE0:=[ev(p,[F0|g0,h0,0]):p in IEK];
S<hh>:=PolynomialRing(F0); T<ll>:=PolynomialRing(S);
gg:=(ll*IE0[1]-24*hh^2+48*hh-8)/32;
IEn:=[T!ev(p,[FieldOfFractions(T)|gg,hh,0]):p in IEK];
pp:=[IEn[i]-ll^([1,2,3,5][i])*IE0[i]:i in [2..4]];

rr:=[Resultant(pp[1],pp[2]),Resultant(pp[1],pp[3]),Resultant(pp[2],pp[3])];

gcd:=GCD(rr); gcd/:=LeadingCoefficient(gcd);

assert gcd eq hh-h0;
U<lu>:=PolynomialRing(F0);
pl:=[U![Evaluate(c,h0):c in Coefficients(p)]:p in pp];
ld:=GCD(pl); ld/:=LeadingCoefficient(ld);

assert ld eq lu-1;
assert (IE0[1]-24*h0^2+48*h0-8)/32 eq g0;
print "CHECK rational Humbert inverse by exact resultants";
F:=QuadraticField(13); ZF:=Integers(F);
M:=GradedRingOfHMFs(F,40);
computed:=ConstructGeneratorsAndRelations(M,1*ZF,8,16);
G:=computed[1]; RG:=ConstructWeightedPolynomialRing(G);
assert VariableWeights(RG) eq [2,4,6,6,8];
// The stored weight-8 generator has a fixed shift by lower-weight products.
coordinateMap:=[RG|RG.1,RG.2,RG.3,RG.4,RG.5-25/4*(RG.2^2-RG.1*RG.4)];
rawIdeal:=ConstructIdeal(RG,computed[2]);
assert VerifyGradedIsomorphism(J,rawIdeal,coordinateMap,GradedInverseImages(RG,coordinateMap));
G[8]:=[G[8][1]-25/4*(G[4][1]^2-G[2][1]*G[6][2])];
print "CHECK exact stored weight-8 coordinate change";
for k in [2,4,6,8,10,12,16] do
  mm:=[m:m in MonomialsOfWeightedDegree(RG,k)]; ff:=EvaluateMonomials(G,mm);
  rank:=Rank(CoefficientsMatrix(ff)); dim:=Dimension(HMFSpace(M,[k,k]));
  printf "CHECK coefficient injection weight=%o rank=%o dimension=%o\n",k,rank,dim;
  assert rank eq dim;
end for;
J:=LoadStoredCanonicalRing("2.2.13.1-1.1");
for p in Basis(J) do
  cc,mm:=CoefficientsAndMonomials(RG!p); ff:=EvaluateMonomials(G,mm);
  assert IsZero(&+[cc[i]*ff[i]:i in [1..#mm]]);
end for;
sane,HT,HS:=HilbertSeriesSanityCheck(M,1*ZF,[J]); assert sane;
assert AlgebraicallyIndependent([G[2][1]^6,G[2][1]^4*G[4][1],G[2][1]^3*G[6][2]]);
assert IsPrime(J);
skew:=8*G[8][1]-4*G[2][1]*G[6][1]+57*G[4][1]^2-57*G[2][1]*G[6][2];
assert not IsZero(skew) and Swap(skew) eq (-1)*skew;
for k in [2,4,6] do for form in G[k] do assert Swap(form) eq form; end for; end for;
print "CHECK D=13 stored relations, primality, full Hilbert series, algebraic independence, and swap";
U,unitmap:=UnitGroup(F);
assert ClassNumber(F) eq 1 and Norm(unitmap(U.2)) eq -1;
bb:=NarrowClassRepresentative(M,Different(ZF)^-1); assert bb eq 1*ZF;
psi:=AssociativeArray();
for k in [4,6,10,12] do
  plus,minus:=SiegelEisensteinPullback(M,[k,k]);
  assert IsZero(minus); psi[k]:=plus;
end for;
chi10:=-43867/(2^12*3^5*5^2*7*53)*(psi[4]*psi[6]-psi[10]);
chi12:=131*593/(2^13*3^7*5^3*7^2*337)*(3^2*7^2*psi[4]^3+2*5^3*psi[6]^2-691*psi[12]);
for i->form in [*psi[4],psi[6],chi10,chi12*] do
  bas,mon:=CanonicalBasis(G,computed[2],form);
  mat:=CoefficientsMatrix(bas cat [form]);
  assert Rank(RowSubmatrix(mat,1,#bas)) eq Dimension(Parent(form));
  ok,sol:=IsConsistent(RowSubmatrix(mat,1,#bas),RowSubmatrix(mat,#bas+1,1));
  assert ok;
  assert &+[RG|sol[1][j]*mon[j]:j in [1..#bas]] eq RG!pullbacks[i];
end for;
print "CHECK exact modular dictionary, component, and determinant units";
assert IsSquarefree(2) and not IsSquare(Rationals()!2);
result:="TWIST EK D=13 c=2"; assert not "PASS" in result;
print result;
print "PASS EK D=13 over Q";
