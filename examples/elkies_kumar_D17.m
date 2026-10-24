// Certify the D=17 function-field comparison and its modular dictionary over Q.
SetNthreads(1);
SetMemoryLimit(16*1024^3);
SetColumns(0);
W:=eval Read("Verification/ElkiesKumar/2.2.17.1-1.1.m");
P,K,Q,L,f,Z,B,phiFF,psiFF,pullbacks,hashes,excludedEK,IEK:=Explode(W);
a:=K.1; b:=K.2; t:=K.3; u:=L.1; v:=L.2; z:=L.3;
ev:=func<p,vals|Evaluate(Numerator(p),vals)/Evaluate(Denominator(p),vals)>;
factors:=[p[1]:p in Factorization(Numerator(Z^2-B))|Degree(p[1],3) gt 0];
assert #factors eq 1 and Degree(factors[1],3) eq 2;
Jo:=ideal<P|factors[1]>;
J:=LoadStoredCanonicalRing("2.2.17.1-1.1"); R:=Generic(J);
c:=a*b*(4*b+1)/(a-1)^2;
stored:=[K|1,a*c,c,t,b*c,a*b*c,(2-a)*c^2+b*c-t*b+2*b^2*c];
for p in Basis(J) do
  pp:=ev(p,stored);
  assert Numerator(pp) in Jo and not Denominator(pp) in Jo;
end for;
V:=PolynomialRing(Rationals(),6); FV:=FieldOfFractions(V);
JV:=ideal<V|[Evaluate(p,[V|1] cat [V.i:i in [1..6]]):p in Basis(J)]>;
back:=[FV|FV.1/FV.2,FV.4/FV.2,FV.3];
pp:=ev(Z^2-B,back);
assert Numerator(pp) in JV and not Denominator(pp) in JV;
for i in [2..7] do
  delta:=ev(stored[i],back)-FV.(i-1);
  assert Numerator(delta) in JV and not Denominator(delta) in JV;
end for;
assert [stored[2]/stored[3],stored[5]/stored[3],stored[4]] eq [a,b,t];
print "CHECK both rational compositions for the stored degree-zero chart";
psi4c,psi6c,chi10c,chi12c:=Explode([ev(p,stored):p in pullbacks]);
II:=[K|-24*chi12c/chi10c,4*psi4c,-8*psi6c/3-32*psi4c*chi12c/chi10c,-2^14*chi10c];
scale:=(phiFF[1]+1)^2-4*phiFF[2];
for i in [1..4] do
  delta:=ev(IEK[i],phiFF)-scale^([1,2,3,5][i])*II[i];
  assert Numerator(delta) in Jo and not Denominator(delta) in Jo;
end for;
js:=func<iv|[iv[1]^5/iv[4],iv[1]^3*iv[2]/iv[4],iv[1]^2*iv[3]/iv[4]]>;
for i in [1..3] do
  delta:=ev(js(IEK)[i],phiFF)-js(II)[i];
  assert Numerator(delta) in Jo and not Denominator(delta) in Jo;
end for;
print "CHECK weighted and absolute Igusa identities";
assert &or[IsOdd(e[2]):e in Factorization(f)];
q:=2*a^4*b*(4*b+1)^2/(a-1)^4;
assert B/ev(f,phiFF) eq q^2;
print "CHECK degree two and rational square factor";
for d in [1,2] do
  fs:=[p[1]:p in Factorization(Numerator(Z^2-d*B))|Degree(p[1],3) gt 0];
  assert #fs eq 1 and Degree(fs[1],3) eq 2;
  JD:=ideal<P|fs[1]>; JE:=ideal<Q|Q.3^2-d*f>;
  assert Numerator(ev(Q.3^2-d*f,phiFF)) in JD;
  assert Numerator(ev(Z^2-d*B,psiFF)) in JE;
  for i in [1..3] do
    delta:=ev(psiFF[i],phiFF)-K.i;
    assert Numerator(delta) in JD and not Denominator(delta) in JD;
    delta:=ev(phiFF[i],psiFF)-L.i;
    assert Numerator(delta) in JE and not Denominator(delta) in JE;
  end for;
  deck:=[K|a,b,t-2*Z];
  assert ev(Z^2-d*B,deck) eq Z^2-d*B;
  assert [ev(p,deck):p in phiFF] eq [phiFF[1],phiFF[2],-phiFF[3]];
  assert d*B/ev(f,phiFF) eq d*q^2;
  assert d eq 1 or not IsSquare(Rationals()!d);
  print "CHECK both rational compositions and deck action",d;
end for;
for p in [K|a,b,a-1,4*b+1,II[1],II[4],ev(excludedEK,phiFF)] cat phiFF cat stored do
  assert p ne 0;
  assert not Numerator(p) in Jo and not Denominator(p) in Jo;
end for;
for p in [L|u,v,u+1,2*u+1,(u+1)^2-4*v,IEK[1],IEK[4],excludedEK] cat psiFF do assert p ne 0; end for;
assert #hashes eq 2 and &and[#s eq 64:s in hashes];
print "CHECK chart excludes X1*X3=0, a*b*(a-1)*(4*b+1)=0, I2*I10=0, and source bad loci";
F:=QuadraticField(17); ZF:=Integers(F); M:=GradedRingOfHMFs(F,80);
computed:=ConstructGeneratorsAndRelations(M,1*ZF,8,16);
G:=computed[1]; RG:=ConstructWeightedPolynomialRing(G);
assert VariableWeights(RG) eq [2,4,4,6,6,6,8];
coordinateMap:=[RG|RG.1,RG.2,RG.3,RG.4,RG.5,RG.6,RG.7+2*RG.3^2];
rawIdeal:=ConstructIdeal(RG,computed[2]);
assert VerifyGradedIsomorphism(J,rawIdeal,coordinateMap,GradedInverseImages(RG,coordinateMap));
G[8][1]+:=2*G[4][2]^2;
print "CHECK exact stored weight-8 coordinate change";
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
assert AlgebraicallyIndependent([G[2][1]^2,G[4][1],G[4][2]]);
assert IsPrime(J);
swapped:=AssociativeArray();
for k in Keys(G) do swapped[k]:=[Swap(form):form in G[k]]; end for;
swapImages,swapRing:=ChangeOfPresentation(G,swapped);
assert VerifyGradedIsomorphism(J,J,swapImages,swapImages);
swappedChart:=[ev(p,stored):p in swapImages];
assert [swappedChart[2]/swappedChart[3],swappedChart[5]/swappedChart[3]] eq [a,b];
delta:=ev(Z,[K|a,b,swappedChart[4]])+Z;
assert Numerator(delta) in Jo and not Denominator(delta) in Jo;
assert not Numerator(Z) in Jo;
print "CHECK stored relations, primality, full Hilbert series, algebraic independence, and modular swap";
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
print "TWIST EK D=17 c=2 (synthetic fixture)";
print "PASS EK D=17 over Q";
