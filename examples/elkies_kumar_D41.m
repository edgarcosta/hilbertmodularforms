// Certify the D=41 function-field comparison and its modular dictionary over Q.
SetNthreads(1);
SetMemoryLimit(16*1024^3);
SetColumns(0);
W:=eval Read("Verification/ElkiesKumar/2.2.41.1-1.1.m");
P,K,Q,L,f,Z,B,phiFF,psiFF,pullbacks,hashes,excludedEK,IEK,stored,coordinateMap,cachedInStored,reconstruction,retainedQuadratic:=Explode(W);
a:=K.1; b:=K.2; t:=K.3; u:=L.1; v:=L.2; z:=L.3;
ev:=func<p,vals|Evaluate(Numerator(p),vals)/Evaluate(Denominator(p),vals)>;
factors:=[p[1]:p in Factorization(Numerator(Z^2-B))|Degree(p[1],3) gt 0];
assert #factors eq 1 and Degree(factors[1],3) eq 2;
Jo:=ideal<P|factors[1]>;
J:=LoadStoredCanonicalRing("2.2.41.1-1.1"); R:=Generic(J);
F0<aa,bb>:=RationalFunctionField(Rationals(),2); TT<tt>:=PolynomialRing(F0); FF0:=FieldOfFractions(TT);
z0:=ev(Z,[FF0|aa,bb,tt]); b0:=F0!ev(B,[FF0|aa,bb,tt]);
quad0:=TT!(z0^2-b0); EE<root>:=quo<TT|quad0>;
storedEE:=[ev(p,[EE|aa,bb,root]):p in stored];
for p in Basis(J) do assert ev(p,storedEE) eq 0; end for;
FR:=FieldOfFractions(R); raw:=[FR|p:p in cachedInStored];
cu:=raw[2]/R.1; cv:=raw[7]/R.1^2; ct:=raw[4]/R.1^2; ca:=raw[5]/R.1^2; cb:=raw[6]/R.1^2;
retained:=[FR|cu,0,ct,ca,cb,cv,0,0,0,0,0,0];
for i in [2..13] do
  delta:=ev(reconstruction[i-1],retained)-raw[i]/R.1^(WeightedDegree(R.i) div 2);
  assert Numerator(delta) in J and not Denominator(delta) in J;
end for;
assert Numerator(cu^2*ca+(cu^2-cv)*cb+cu^2*cv) in J;
nDD:=R.7^2*R.6^2-4*R.7*R.6^2*R.2^2+4*R.6^2*R.2^4-5*R.6*R.2^6+7*R.7*R.6*R.2^4-4*R.7^2*R.6*R.2^2+R.2^8;
assert nDD-R.1*R.2^3*(R.2^2-R.7)*R.6 in J;
qq:=ev(retainedQuadratic,[FR|cu,cv,ct,ca,cb]);
assert Numerator(qq) in J and not Denominator(qq) in J;
d0:=(aa-2)^2*bb^2+(-5+7*aa-4*aa^2)*bb+1;
u0:=(1-aa)*bb/d0; v0:=u0^2*aa; b0:=u0^2*bb; a0:=u0^2*((aa-1)*bb-aa);
assert ev(retainedQuadratic,[FF0|u0,v0,tt,a0,b0]) eq quad0;
assert [storedEE[7]/storedEE[2]^2,storedEE[6]/storedEE[2]^2,storedEE[4]-storedEE[5]+storedEE[7]] eq [EE|aa,bb,root];
print "CHECK both rational compositions for the stored degree-zero chart";
reducedPullbacks:=[TT!ev(p,storedEE):p in pullbacks];
assert &and[Degree(p) le 0:p in reducedPullbacks];
psi4c,psi6c,chi10c,chi12c:=Explode([K!ev(F0!p,[K|a,b]):p in reducedPullbacks]);
II:=[K|-24*chi12c/chi10c,4*psi4c,-8*psi6c/3-32*psi4c*chi12c/chi10c,-2^14*chi10c];
scale:=phiFF[1]^2*(4*phiFF[2]+1)^2-16*phiFF[1]*phiFF[2]+8*phiFF[1]+256*phiFF[2]+16;
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
DD:=(a-2)^2*b^2+(-5+7*a-4*a^2)*b+1;
q:=(a-1)^3*b^3/(32*DD^2);
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
for p in [K|a,b,a-1,a-2,b-1,DD,II[1],II[4],ev(excludedEK,phiFF)] cat phiFF cat stored do
  assert p ne 0;
  assert not Numerator(p) in Jo and not Denominator(p) in Jo;
end for;
for p in [L|u,v,u-4,u+4,u^2*(4*v+1)^2-16*u*v+8*u+256*v+16,IEK[1],IEK[4],excludedEK] cat psiFF do assert p ne 0; end for;
assert #hashes eq 2 and &and[#s eq 64:s in hashes];
print "CHECK chart excludes X1*X2=0, a*b*(a-1)*(a-2)*(b-1)*DD=0, I2*I10=0, and source bad loci";
F:=QuadraticField(41); ZF:=Integers(F); M:=GradedRingOfHMFs(F,160);
computed:=ConstructGeneratorsAndRelations(M,1*ZF,8,16);
G:=computed[1]; RG:=ConstructWeightedPolynomialRing(G);
assert VariableWeights(RG) eq [2,2,4,4,4,4,4,6,6,6,6,6,8];
coordinateMap:=[RG!p:p in coordinateMap];
rawIdeal:=ConstructIdeal(RG,computed[2]);
assert VerifyGradedIsomorphism(J,rawIdeal,coordinateMap,GradedInverseImages(RG,coordinateMap));
storedG:=AssociativeArray();
for p in coordinateMap do
  k:=WeightedDegree(p);
  cc,mm:=CoefficientsAndMonomials(p); ff:=EvaluateMonomials(G,mm);
  form:=&+[cc[j]*ff[j]:j in [1..#mm]];
  if not IsDefined(storedG,k) then storedG[k]:=[]; end if;
  Append(~storedG[k],form);
end for;
G:=storedG;
print "CHECK exact stored coordinate change on all thirteen generators";
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
assert AlgebraicallyIndependent([G[2][1]^2,G[2][1]*G[2][2],G[4][5]]);
// Saturation transfers the domain property of the irreducible quadratic chart.
// The two chart compositions identify these localizations in every generator.
for p in [R|R.1,R.2,R.6,R.7,R.7-R.2^2,2*R.2^2-R.7,R.6-R.2^2] do
  assert Saturation(J,ideal<R|p>) eq J;
end for;
open:=P!(a*b*(a-1)*(a-2)*(b-1)*DD);
for p in stored do
  den:=Denominator(p);
  repeat
    common:=GCD(den,open); den:=ExactQuotient(den,common);
  until Degree(common) eq 0;
  assert Degree(den) eq 0;
end for;

print "CHECK domain by irreducible chart and saturation at every chart divisor";
swapped:=AssociativeArray();
for k in Keys(G) do swapped[k]:=[Swap(form):form in G[k]]; end for;
swapImages,swapRing:=ChangeOfPresentation(G,swapped);
assert VerifyGradedIsomorphism(J,J,swapImages,swapImages);
swappedChart:=[ev(p,stored):p in swapImages];
assert [swappedChart[7]/swappedChart[2]^2,swappedChart[6]/swappedChart[2]^2] eq [a,b];
delta:=ev(Z,[K|a,b,swappedChart[4]-swappedChart[5]+swappedChart[7]])+Z;
assert Numerator(delta) in Jo and not Denominator(delta) in Jo;
assert not Numerator(Z) in Jo;
print "CHECK stored relations, domain, full Hilbert series, algebraic independence, and modular swap";
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
print "TWIST EK D=41 c=2 (synthetic fixture)";
print "PASS EK D=41 over Q";
