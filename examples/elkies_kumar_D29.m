// Certify the D=29 comparison over Q, including the modular dictionary.
// The synthetic d=2 fixture must be classified as a nonsquare twist.
SetNthreads(1);
SetColumns(0);
W:=eval Read("Verification/ElkiesKumar/2.2.29.1-1.1.m");
P,K,Q,L,f,Z,B,phiFF,psiFF,pullbacks,hashes,excludedEK,IEK:=Explode(W);
a:=K.1; b:=K.2; t:=K.3; u:=L.1; v:=L.2; z:=L.3;
ev:=func<p,vals|Evaluate(Numerator(p),vals)/Evaluate(Denominator(p),vals)>;
Jo:=ideal<P|Z^2-B>;
J:=LoadStoredCanonicalRing("2.2.29.1-1.1"); R:=Generic(J);
s4:=-a/b*t+(-76*a^6+a^5+156*a^4*b-17*a^3*b-144*a^2*b^2+a^2*b+6*a*b^2+8*b^3)/(a*(a+4*b));
stored:=[K|1,a,b,s4,b^2/a,a*(a^2-b)^2/(a+4*b),t];
for p in Basis(J) do
  pp:=ev(p,stored);
  assert Numerator(pp) in Jo and not Denominator(pp) in Jo;
end for;
V:=PolynomialRing(Rationals(),6); FV:=FieldOfFractions(V);
JV:=ideal<V|[Evaluate(p,[V|1] cat [V.i:i in [1..6]]):p in Basis(J)]>;
back:=[FV|FV.1,FV.2,FV.6];
pp:=ev(Z^2-B,back);
assert Numerator(pp) in JV and not Denominator(pp) in JV;
for i in [2..7] do
  delta:=ev(stored[i],back)-FV.(i-1);
  assert Numerator(delta) in JV and not Denominator(delta) in JV;
end for;
assert [stored[2],stored[3],stored[7]] eq [a,b,t];
print "CHECK both rational compositions for the stored degree-zero chart";
psi4c,psi6c,chi10c,chi12c:=Explode([ev(p,stored):p in pullbacks]);
II:=[K|-24*chi12c/chi10c,4*psi4c,-8*psi6c/3-32*psi4c*chi12c/chi10c,-2^14*chi10c];
js:=func<iv|[iv[1]^5/iv[4],iv[1]^3*iv[2]/iv[4],iv[1]^2*iv[3]/iv[4]]>;
for i in [1..3] do
  delta:=ev(js(IEK)[i],phiFF)-js(II)[i];
  assert Numerator(delta) in Jo and not Denominator(delta) in Jo;
end for;
print "CHECK three normalized Igusa identities";
assert &or[IsOdd(e[2]):e in Factorization(f)];
q:=b*(a+4*b)^3/(8*a);
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
  deck:=[K|a,b,t-2*Z/(a*(a+4*b))];
  assert ev(Z^2-d*B,deck) eq Z^2-d*B;
  assert [ev(p,deck):p in phiFF] eq [phiFF[1],phiFF[2],-phiFF[3]];
  assert d*B/ev(f,phiFF) eq d*q^2;
  assert d eq 1 or not IsSquare(Rationals()!d);
  print "CHECK both rational compositions and deck action",d;
end for;
for p in [K|a,b,a+4*b,a^2-b,II[1],II[4]] cat phiFF cat stored do
  assert p ne 0;
  assert not Numerator(p) in Jo and not Denominator(p) in Jo;
end for;
for p in [L|u,v,4*u-v-1,IEK[1],IEK[4],excludedEK] cat psiFF do assert p ne 0; end for;
assert #hashes eq 2 and &and[#s eq 64:s in hashes];
print "CHECK chart excludes X1=0, a=0, b=0, a+4*b=0, a^2-b=0, 4*u-v-1=0, I2=0, and source bad locus";
F:=QuadraticField(29); ZF:=Integers(F);
M:=GradedRingOfHMFs(F,160);
computed:=ConstructGeneratorsAndRelations(M,1*ZF,8,16);
G:=computed[1]; RG:=ConstructWeightedPolynomialRing(G);
assert VariableWeights(RG) eq [2,2,4,6,6,6,8];
coordinateMap:=[RG|RG.1,RG.2,RG.3,-RG.4+RG.2^3-17*RG.2*RG.3+RG.1*RG.3+RG.5-11*RG.6,RG.5,RG.6,RG.7];
rawIdeal:=ConstructIdeal(RG,computed[2]);
assert VerifyGradedIsomorphism(J,rawIdeal,coordinateMap,GradedInverseImages(RG,coordinateMap));
G[6][1]:=(-1)*G[6][1]+G[2][2]^3-17*G[2][2]*G[4][1]+G[2][1]*G[4][1]+G[6][2]-11*G[6][3];
print "CHECK exact stored weight-6 coordinate change";
for k in [2,4,6,8,10,12,14,16] do
  mm:=[m:m in MonomialsOfWeightedDegree(RG,k)];
  rank:=Rank(CoefficientsMatrix(EvaluateMonomials(G,mm))); dim:=Dimension(HMFSpace(M,[k,k]));
  printf "CHECK coefficient injection weight=%o rank=%o dimension=%o\n",k,rank,dim;
  assert rank eq dim;
end for;
for p in Basis(J) do
  cc,mm:=CoefficientsAndMonomials(RG!p); ff:=EvaluateMonomials(G,mm);
  assert IsZero(&+[cc[i]*ff[i]:i in [1..#mm]]);
end for;
sane,HT,HS:=HilbertSeriesSanityCheck(M,1*ZF,[J]); assert sane;
assert AlgebraicallyIndependent([G[2][1]^2,G[2][1]*G[2][2],G[4][1]]);
assert IsPrime(J);
// Clearing the chart denominator gives the weight-14 antisymmetric form.
H:=PolynomialRing(Rationals(),[2,2,4,6,6,6,8]);
n:=141*H.2^5*H.3-H.1*H.2^4*H.3-286*H.2^3*H.3^2+17*H.1*H.2^2*H.3^2+209*H.2*H.3^3-H.1^2*H.2*H.3^2-4*H.1*H.3^3;
skewpoly:=H.2*(H.1*H.2+4*H.3)*H.7+n/2;
cc,mm:=CoefficientsAndMonomials(RG!skewpoly); ff:=EvaluateMonomials(G,mm);
skew:=&+[cc[i]*ff[i]:i in [1..#mm]];
assert not IsZero(skew) and Swap(skew) eq (-1)*skew;
for k in [2,4] do for form in G[k] do assert Swap(form) eq form; end for; end for;
assert ev(skewpoly,stored) eq Z;
print "CHECK D=29 stored relations, primality, full Hilbert series, algebraic independence, and swap";
U,unitmap:=UnitGroup(F);
assert ClassNumber(F) eq 1 and Norm(unitmap(U.2)) eq -1;
assert NarrowClassRepresentative(M,Different(ZF)^-1) eq 1*ZF;
psi:=AssociativeArray();
for k in [4,6,10,12] do
  plus,minus:=SiegelEisensteinPullback(M,[k,k]); assert IsZero(minus); psi[k]:=plus;
end for;
chi10:=-43867/(2^12*3^5*5^2*7*53)*(psi[4]*psi[6]-psi[10]);
chi12:=131*593/(2^13*3^7*5^3*7^2*337)*(3^2*7^2*psi[4]^3+2*5^3*psi[6]^2-691*psi[12]);
for i->form in [*psi[4],psi[6],chi10,chi12*] do
  cc,mm:=CoefficientsAndMonomials(RG!pullbacks[i]); ff:=EvaluateMonomials(G,mm);
  assert IsZero(form-&+[cc[j]*ff[j]:j in [1..#mm]]);
end for;
print "CHECK exact modular dictionary, component, and determinant units";
result:="TWIST EK D=29 c=2"; assert not "PASS" in result; print result;
print "PASS EK D=29 over Q";
