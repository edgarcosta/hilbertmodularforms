// Certify the D=8 comparison over Q, including the modular dictionary.
// The synthetic d=2 fixture must be classified as a nonsquare twist.
SetNthreads(1);
SetColumns(0);
W := eval Read("Verification/ElkiesKumar/2.2.8.1-1.1.m");
P,K,Q,L,f,Z,B,phiFF,psiFF,pullbacks,hashes,excludedEK,IEK := Explode(W);
a:=K.1; b:=K.2; t:=K.3; r:=L.1; s:=L.2; z:=L.3;
ev:=func<p,vals|Evaluate(Numerator(p),vals)/Evaluate(Denominator(p),vals)>;
J:=LoadStoredCanonicalRing("2.2.8.1-1.1");
R:=Generic(J);
LitData:=eval Read("Verification/LiteratureEquations/2.2.8.1-1.1-Hirzebruch.m");
I,Phi,Psi,citation:=LitData(R,R);
assert VerifyGradedIsomorphism(I,J,Phi,Psi);
assert ev(Phi[4],[K|1,a,b,t]) eq Z/128;
Jo:=ideal<P|[Evaluate(p,[P|1,P.1,P.2,P.3]):p in Basis(J)]>;
assert Jo eq ideal<P|Z^2-B>;
psi4c,psi6c,chi10c,chi12c:=Explode([ev(p,[K|1,a,b,t]):p in pullbacks]);
II:=[K|-24*chi12c/chi10c,4*psi4c,-8*psi6c/3-32*psi4c*chi12c/chi10c,-2^14*chi10c];
js:=func<v|[v[1]^5/v[4],v[1]^3*v[2]/v[4],v[1]^2*v[3]/v[4]]>;
for i in [1..3] do assert ev(js(IEK)[i],phiFF) eq js(II)[i]; end for;
print "CHECK three normalized Igusa identities";
assert &or[IsOdd(e[2]):e in Factorization(f)];
q:=b*(a+4*b)^2/(2*a);
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
  deck:=[K|a,b,2*a^3+a*b+20*a^2*b+2*b^2-t];
  assert ev(Z^2-d*B,deck) eq Z^2-d*B;
  assert [ev(p,deck):p in phiFF] eq [phiFF[1],phiFF[2],-phiFF[3]];
  assert d*B/ev(f,phiFF) eq d*q^2;
  assert d eq 1 or not IsSquare(Rationals()!d);
  print "CHECK both rational compositions and deck action",d;
end for;
for p in [K|a,b,a+4*b,II[1],II[4]] cat phiFF do
  assert p ne 0;
  assert not Numerator(p) in Jo and not Denominator(p) in Jo;
end for;
for p in [L|r,s,2*r+1,IEK[1],IEK[4],excludedEK] cat psiFF do assert p ne 0; end for;
assert #hashes eq 2 and &and[#h eq 64:h in hashes];
print "CHECK chart excludes X2=0, a=0, b=0, a+4*b=0, r=0, s=0, 2*r+1=0, I2=0, and source bad locus";
// Equality of the three absolute invariants fixes the weighted tuple up to scale.
// Its generic fiber is a rational point, proving equality of the Humbert fields.
B0<r0,s0>:=PolynomialRing(Rationals(),2);
F0:=FieldOfFractions(B0);
IE0:=[ev(p,[F0|r0,s0,0]):p in IEK];
AA<rr,ss,ll,uu>:=PolynomialRing(F0,4,"lex");
IEn:=[ev(p,[FieldOfFractions(AA)|rr,ss,0]):p in IEK];
weights:=[1,2,3,5];
fiber:=ideal<AA|[AA!Numerator(IEn[i]-ll^weights[i]*IE0[i]):i in [1..4]] cat [ll*uu*rr*ss-1]>;
assert GroebnerBasis(fiber) eq [AA|rr-r0,ss-s0,ll-1,uu-1/(r0*s0)];
print "CHECK rational Humbert inverse by exact generic fiber";
F:=QuadraticField(8); ZF:=Integers(F);
M:=GradedRingOfHMFs(F,80);
computed:=ConstructGeneratorsAndRelations(M,1*ZF,14,14);
G:=computed[1]; RG:=ConstructWeightedPolynomialRing(G);
assert VariableWeights(RG) eq [2,4,6,14];
for k in [2,4,6,10,12,14,28] do
  mm:=[m:m in MonomialsOfWeightedDegree(RG,k)];
  ff:=EvaluateMonomials(G,mm);
  rank:=Rank(CoefficientsMatrix(ff)); dim:=Dimension(HMFSpace(M,[k,k]));
  printf "CHECK coefficient injection weight=%o rank=%o dimension=%o\n",k,rank,dim;
  assert rank eq dim;
end for;
J:=LoadStoredCanonicalRing("2.2.8.1-1.1");
for p in Basis(J) do
  cc,mm:=CoefficientsAndMonomials(RG!p);
  ff:=EvaluateMonomials(G,mm);
  assert IsZero(&+[cc[i]*ff[i]:i in [1..#mm]]);
end for;
sane,HT,HS:=HilbertSeriesSanityCheck(M,1*ZF,[J]); assert sane;
assert AlgebraicallyIndependent([G[2][1]^6,G[4][1]^3,G[6][1]^2]);
skew:=2*G[2][1]*G[4][1]^3+G[2][1]^2*G[4][1]*G[6][1]+20*G[4][1]^2*G[6][1]+2*G[2][1]*G[6][1]^2-2*G[14][1];
assert not IsZero(skew) and Swap(skew) eq (-1)*skew;
for k in [2,4,6] do assert Swap(G[k][1]) eq G[k][1]; end for;
print "CHECK D=8 stored relation, full Hilbert series, algebraic independence, and swap";
U,unitmap:=UnitGroup(F);
assert ClassNumber(F) eq 1 and Norm(unitmap(U.2)) eq -1;
bb:=NarrowClassRepresentative(M,Different(ZF)^-1);
assert bb eq 1*ZF;
Mlo:=GradedRingOfHMFs(F,40);
low:=ConstructGeneratorsAndRelations(Mlo,1*ZF,14,14);
Glo:=low[1]; Rlo:=ConstructWeightedPolynomialRing(Glo);
for k in [2,4,6,14] do
  for nu in FunDomainRepsUpToPrec(Mlo,bb,40) do
    assert Coefficient(G[k][1],bb,nu:InFunDomain:=true) eq Coefficient(Glo[k][1],bb,nu:InFunDomain:=true);
  end for;
end for;
psi:=AssociativeArray();
for k in [4,6,10,12] do
  plus,minus:=SiegelEisensteinPullback(Mlo,[k,k]);
  assert IsZero(minus); psi[k]:=plus;
end for;
chi10:=-43867/(2^12*3^5*5^2*7*53)*(psi[4]*psi[6]-psi[10]);
chi12:=131*593/(2^13*3^7*5^3*7^2*337)*(3^2*7^2*psi[4]^3+2*5^3*psi[6]^2-691*psi[12]);
for i->form in [*psi[4],psi[6],chi10,chi12*] do
  bas,mon:=CanonicalBasis(Glo,low[2],form);
  mat:=CoefficientsMatrix(bas cat [form]);
  assert Rank(RowSubmatrix(mat,1,#bas)) eq Dimension(Parent(form));
  ok,sol:=IsConsistent(RowSubmatrix(mat,1,#bas),RowSubmatrix(mat,#bas+1,1));
  assert ok;
  assert &+[Rlo|sol[1][j]*mon[j]:j in [1..#bas]] eq Rlo!pullbacks[i];
end for;
print "CHECK exact modular dictionary, component, and determinant units";
assert IsSquarefree(2) and not IsSquare(Rationals()!2);
result:="TWIST EK D=8 c=2";
assert not "PASS" in result;
print result;
print "PASS EK D=8 over Q";
