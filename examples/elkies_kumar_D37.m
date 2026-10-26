// Certify the D=37 comparison over Q, including the modular dictionary.
// The synthetic d=2 fixture must be classified as a nonsquare twist.
SetNthreads(1);
SetColumns(0);
W:=eval Read("Verification/ElkiesKumar/2.2.37.1-1.1.m");
P,K,Q,L,f,Z,B,phiFF,psiFF,pullbacks,hashes,excludedEK,IEK:=Explode(W);
a:=K.1; b:=K.2; t:=K.3; u:=L.1; v:=L.2; z:=L.3;
ev:=func<p,vals|Evaluate(Numerator(p),vals)/Evaluate(Denominator(p),vals)>;
factors:=[p[1]:p in Factorization(Z^2-B)|Degree(p[1],3) gt 0];
assert #factors eq 1 and Degree(factors[1],3) eq 2;
Jo:=ideal<P|factors[1]>;
J:=LoadStoredCanonicalRing("2.2.37.1-1.1"); R:=Generic(J);
H:=PolynomialRing(Rationals(),[2,2,4,4,6,6,6,6,6,8,8]);
coordinateMap:=[H|
H.1,
H.2,
H.3,
H.4,
H.2^3 + H.1*H.3 - 19/5*H.2*H.3 - H.2*H.4 - H.5 - 4*H.7 - 12*H.8 + 96*H.9,
H.6 + 3*H.7 - 2*H.8 - 15*H.9,
H.7 - 3*H.9,
H.8 - 4*H.9,
-H.9,
-24*H.2^2*H.3 - 4*H.2^2*H.4 + 27*H.3*H.4 - 706/5*H.4^2 - 3*H.2*H.6 + H.1*H.7 + 3*H.2*H.8 + 27*H.1*H.9 + 452/5*H.2*H.9 - H.10,
-27/4*H.2^2*H.3 + H.3^2 + 5*H.2^2*H.4 + 27/4*H.3*H.4 - 9*H.4^2 + 5*H.2*H.6 + 19*H.2*H.8 + 7/4*H.1*H.9 + 8/5*H.2*H.9 - H.11
];
rawImages:=GradedInverseImages(H,coordinateMap);
stored:=[K|
1,
a,
(a^4 + 6/5*a^2*b + a*b - 3*b^2)/(a^2 - b),
b,
(-21/20*a^4 - 1/4*a^3 + 23/10*a^2*b + 1/4*a*b - 5/4*b^2)/(a^5 - 14/5*a^3*b - 1/4*a^2*b + 2*a*b^2)*t + (2791/64*a^14 + 255/64*a^13 - 20019/160*a^12*b + 2659/64*a^11*b - 101739/1600*a^10*b^2 + 45/8*a^10*b - 30291/160*a^9*b^2 + 242753/400*a^8*b^3 - 161/32*a^8*b^2 + 41003/160*a^7*b^3 + 105/64*a^7*b^2 - 260619/320*a^6*b^4 - 649/64*a^6*b^3 - 7533/64*a^5*b^4 - 45/32*a^5*b^3 + 64037/160*a^4*b^5 + 85/8*a^4*b^4 - 497/64*a^3*b^5 - 1333/64*a^2*b^6 - 105/64*a^2*b^5 + 215/16*a*b^6 - 215/8*b^7)/(a^11 + 5/16*a^10 - 121/20*a^9*b - 7/4*a^8*b + 73/5*a^7*b^2 - 5/64*a^7*b + 7/2*a^6*b^2 - 351/20*a^5*b^3 + 5/32*a^5*b^2 - 3*a^4*b^3 + 21/2*a^3*b^4 - 5/64*a^3*b^3 + 15/16*a^2*b^4 - 5/2*a*b^5),
(1/4*a^4 - 1/2*a^2*b + 1/4*b^2)/(a^5 - 14/5*a^3*b - 1/4*a^2*b + 2*a*b^2)*t + (-351/64*a^10 + 5/16*a^9 - 203/80*a^8*b - 121/16*a^7*b + 23107/800*a^6*b^2 + 15/64*a^6*b + 119/40*a^5*b^2 - 1093/80*a^4*b^3 - 69/32*a^4*b^2 + 179/16*a^3*b^3 - 5/64*a^3*b^2 - 1103/64*a^2*b^4 + 65/64*a^2*b^3 - 85/16*a*b^4 + 75/8*b^5)/(a^7 + 5/16*a^6 - 81/20*a^5*b - 9/8*a^4*b + 11/2*a^3*b^2 - 5/64*a^3*b + 15/16*a^2*b^2 - 5/2*a*b^3),
(-15/16*a^6 - 9/8*a^4*b - 15/16*a^3*b + 29/16*a^2*b^2 - 5/16*a*b^2 + 5/4*b^3)/(a^3 + 5/16*a^2 - 5/4*a*b),
(-15/16*a^9 + 7/4*a^7*b - 5/8*a^6*b + 163/40*a^5*b^2 + 13/4*a^4*b^2 - 45/4*a^3*b^3 + 5/16*a^3*b^2 - 25/8*a^2*b^3 + 105/16*a*b^4)/(a^6 + 5/16*a^5 - 13/4*a^4*b - 5/8*a^3*b + 7/2*a^2*b^2 + 5/16*a*b^2 - 5/4*b^3),
(-5/16*a^5 - 3/8*a^3*b - 5/16*a^2*b + 15/16*a*b^2)/(a^2 + 5/16*a - 5/4*b),
(1/4*a^4*b - 1/2*a^2*b^2 + 1/4*b^3)/(a^6 - 14/5*a^4*b - 1/4*a^3*b + 2*a^2*b^2)*t + (-5/16*a^12 + 357/64*a^10*b - 15/64*a^9*b - 2473/40*a^8*b^2 - 783/64*a^7*b^2 + 25393/160*a^6*b^3 + 5/64*a^6*b^2 + 1407/64*a^5*b^3 - 11729/80*a^4*b^4 - 5/16*a^4*b^3 - 517/64*a^3*b^4 + 2553/64*a^2*b^5 - 5/64*a^2*b^4 - 15/16*a*b^5 + 35/8*b^6)/(a^8 + 5/16*a^7 - 81/20*a^6*b - 9/8*a^5*b + 11/2*a^4*b^2 - 5/64*a^4*b + 15/16*a^3*b^2 - 5/2*a^2*b^3),
(1/4*a^4 + 3/10*a^2*b + 1/4*a*b - 3/4*b^2)/(a^4 - 14/5*a^2*b - 1/4*a*b + 2*b^2)*t + (-11/64*a^14 + 5/16*a^13 - 1849/160*a^12*b - 27/8*a^11*b - 12613/1600*a^10*b^2 + 35/64*a^10*b - 9799/320*a^9*b^2 + 178881/2000*a^8*b^3 - 217/32*a^8*b^2 + 10799/400*a^7*b^3 + 5/32*a^7*b^2 - 23517/1600*a^6*b^4 - 5681/320*a^6*b^3 + 18817/160*a^5*b^4 - 229/64*a^5*b^3 - 32513/160*a^4*b^5 + 159/4*a^4*b^4 - 5/64*a^4*b^3 - 2403/16*a^3*b^5 + 45/32*a^3*b^4 + 12189/64*a^2*b^6 - 85/8*a^2*b^5 + 2245/64*a*b^6 - 165/4*b^7)/(a^10 + 5/16*a^9 - 121/20*a^8*b - 7/4*a^7*b + 73/5*a^6*b^2 - 5/64*a^6*b + 7/2*a^5*b^2 - 351/20*a^4*b^3 + 5/32*a^4*b^2 - 3*a^3*b^3 + 21/2*a^2*b^4 - 5/64*a^2*b^3 + 15/16*a*b^4 - 5/2*b^5)
];
for p in Basis(J) do
  pp:=ev(p,stored);
  assert Numerator(pp) in Jo and not Denominator(pp) in Jo;
end for;
V:=PolynomialRing(Rationals(),10); FV:=FieldOfFractions(V);
JV:=ideal<V|[Evaluate(p,[V|1] cat [V.i:i in [1..10]]):p in Basis(J)]>;
back:=[FV|FV.1,FV.3,ev(rawImages[11],[FV|1] cat [FV.i:i in [1..10]])];
pp:=ev(Z^2-B,back);
assert Numerator(pp) in JV and not Denominator(pp) in JV;
for i in [2..11] do
  delta:=ev(stored[i],back)-FV.(i-1);
  assert Numerator(delta) in JV and not Denominator(delta) in JV;
end for;
assert [stored[2],stored[4]] eq [a,b];
delta:=ev(rawImages[11],stored)-t;
assert Numerator(delta) in Jo and not Denominator(delta) in Jo;
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
C2:=a^2+5/16*a-5/4*b;
C4:=a^4-14/5*a^2*b-1/4*a*b+2*b^2;
q:=25/128*(a^2-b)^5*C4/C2;
assert B/ev(f,phiFF) eq q^2;
print "CHECK degree two and rational square factor";
for d in [1,2] do
  factors:=[p[1]:p in Factorization(Z^2-d*B)|Degree(p[1],3) gt 0];
  assert #factors eq 1 and Degree(factors[1],3) eq 2;
  JD:=ideal<P|factors[1]>; JE:=ideal<Q|Q.3^2-d*f>;
  assert Numerator(ev(Q.3^2-d*f,phiFF)) in JD;
  assert Numerator(ev(P!Z^2-d*B,psiFF)) in JE;
  for i in [1..3] do
    delta:=ev(psiFF[i],phiFF)-K.i;
    assert Numerator(delta) in JD and not Denominator(delta) in JD;
    delta:=ev(phiFF[i],psiFF)-L.i;
    assert Numerator(delta) in JE and not Denominator(delta) in JE;
  end for;
  D0:=Evaluate(Derivative(Z,3),[K|a,b,t]);
  deck:=[K|a,b,t-2*Z/D0];
  assert ev(Z^2-d*B,deck) eq Z^2-d*B;
  assert [ev(p,deck):p in phiFF] eq [phiFF[1],phiFF[2],-phiFF[3]];
  assert d*B/ev(f,phiFF) eq d*q^2;
  assert d eq 1 or not IsSquare(Rationals()!d);
  print "CHECK both rational compositions and deck action",d;
end for;
for p in [K|a,b,a^2-b,C2,C4,II[1],II[4]] cat phiFF cat stored do
  assert p ne 0;
  assert not Numerator(p) in Jo and not Denominator(p) in Jo;
end for;
for p in [L|u,v,4*u+5*v^2+16*v-4,IEK[1],IEK[4],excludedEK] cat psiFF do assert p ne 0; end for;
assert #hashes eq 2 and &and[#s eq 64:s in hashes];
print "CHECK chart excludes X1=0, a=0, b=0, a^2-b=0, C2=0, C4=0, 4*u+5*v^2+16*v-4=0, I2=0, and source bad locus";
F:=QuadraticField(37); ZF:=Integers(F);
M:=GradedRingOfHMFs(F,160);
computed:=ConstructGeneratorsAndRelations(M,1*ZF,8,16);
G:=computed[1]; RG:=ConstructWeightedPolynomialRing(G);
assert VariableWeights(RG) eq [2,2,4,4,6,6,6,6,6,8,8];
coordinateMap:=[RG|RG!p:p in coordinateMap];
rawIdeal:=ConstructIdeal(RG,computed[2]);
assert VerifyGradedIsomorphism(J,rawIdeal,coordinateMap,GradedInverseImages(RG,coordinateMap));
storedG:=AssociativeArray();
for i->p in coordinateMap do
  k:=VariableWeights(RG)[i];
  cc,mm:=CoefficientsAndMonomials(p); ff:=EvaluateMonomials(G,mm);
  form:=&+[cc[j]*ff[j]:j in [1..#mm]];
  if not IsDefined(storedG,k) then storedG[k]:=[]; end if;
  Append(~storedG[k],form);
end for;
G:=storedG;
print "CHECK exact stored coordinate change on all eleven generators";
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
assert AlgebraicallyIndependent([G[2][1]^2,G[2][1]*G[2][2],G[4][2]]);
swapped:=AssociativeArray();
for k in Keys(G) do swapped[k]:=[Swap(form):form in G[k]]; end for;
swapImages,swapRing:=ChangeOfPresentation(G,swapped);
assert VerifyGradedIsomorphism(J,J,swapImages,swapImages);
swappedChart:=[ev(p,stored):p in swapImages];
assert [swappedChart[2],swappedChart[4]] eq [a,b];
newt:=ev(rawImages[11],swappedChart);
delta:=ev(Z,[K|a,b,newt])+Z;
assert Numerator(delta) in Jo and not Denominator(delta) in Jo;
assert not Numerator(Z) in Jo;
print "CHECK exact modular swap on all stored generators";
print "CHECK D=37 stored relations, full Hilbert series, algebraic independence, and swap";
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
// Williams' complete presentation is a ring of modular forms.
// Its even subring and this verified isomorphic presentation are domains.
LitData:=eval Read("Verification/LiteratureEquations/2.2.37.1-1.1-Williams.m");
S:=PolynomialRing(Rationals(),VariableWeights(R));
I,litPhi,litPsi,citation:=LitData(S,R);
assert HilbertSeries(I) eq HilbertSeries(J);
assert VerifyGradedIsomorphism(ideal<S|MinimalBasis(I)>,ideal<R|MinimalBasis(J)>,litPhi,litPsi);
print "CHECK complete Williams even-ring presentation and domain certificate";
result:="TWIST EK D=37 c=2"; assert not "PASS" in result; print result;
print "PASS EK D=37 over Q";
