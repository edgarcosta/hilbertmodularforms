// Certify the D=5 comparison over Q, including the modular dictionary.
// The synthetic d=2 fixture must be classified as a nonsquare twist.
SetNthreads(1);
SetColumns(0);
W := eval Read("Verification/ElkiesKumar/2.2.5.1-1.1.m");
P,K,Q,L,f,Z,B,phiFF,psiFF,pullbacks,hashes,excludedEK,IEK := Explode(W);
a := K.1; b := K.2; t := K.3;
g := L.1; h := L.2; z := L.3;
ev := func<p,vals|Evaluate(Numerator(p),vals)/Evaluate(Denominator(p),vals)>;
J := LoadStoredCanonicalRing("2.2.5.1-1.1");
R := Generic(J);
LitData := eval Read("Verification/LiteratureEquations/2.2.5.1-1.1-Hirzebruch.m");
I,Phi,Psi,citation := LitData(R,R);
assert VerifyGradedIsomorphism(I,J,Phi,Psi);
assert ev(Phi[4],[K|1,a,b,t]) eq Z;
Jo := ideal<P|[Evaluate(p,[P|1,P.1,P.2,P.3]) : p in Basis(J)]>;
assert Jo eq ideal<P|Z^2-B>;
II := [K|24*a^2/b-16, 4, 32*a^2/b-24+2304*a,4096*b];
assert IEK eq [L|24*g+6,9*g^2,81*g^3+18*g^2+36*h,4*h^2];
js := func<v|[v[1]^5/v[4],v[1]^3*v[2]/v[4],v[1]^2*v[3]/v[4]]>;
for i in [1..3] do
  assert ev(js(IEK)[i],phiFF) eq js(II)[i];
end for;
j := js(IEK);
r := j[2]/j[1];
s := j[3]/j[1];
AA := 6*s-2*r;
k := (1944-j[1]*(AA^2+4*r^3))/(7776-2*j[1]*AA*r);
assert k/(1-4*k) eq g;
assert (AA-r*k)/(1-4*k)^3 eq h;
print "CHECK three normalized Igusa identities and rational Humbert inverse";
assert &or[IsOdd(e[2]) : e in Factorization(f)];
print "CHECK degree two";
assert ev(f,phiFF)*(2^23*a^5/b)^2 eq B;
print "CHECK rational square factor";
F := QuadraticField(5);
ZF := Integers(F);
assert ClassNumber(F) eq 1;
U,unitmap := UnitGroup(F);
assert Norm(unitmap(U.2)) eq -1;
M := GradedRingOfHMFs(F,80);
bb := NarrowClassRepresentative(M,Different(ZF)^-1);
assert bb eq 1*ZF;
computed := ConstructGeneratorsAndRelations(M,1*ZF,20,20);
G := computed[1];
RG := ConstructWeightedPolynomialRing(G);
assert VariableWeights(RG) eq [2,6,10,20];
for weight in [2,4,6,10,12,20,40] do
  mm := [m : m in MonomialsOfWeightedDegree(RG,weight)];
  fm := EvaluateMonomials(G,mm);
  dimension := Dimension(HMFSpace(M,[weight,weight]));
  rank := Rank(CoefficientsMatrix(fm));
  printf "CHECK coefficient injection weight=%o rank=%o dimension=%o\n",weight,rank,dimension;
  assert rank eq dimension;
end for;
for p in Basis(J) do
  coeffs,mon := CoefficientsAndMonomials(RG!p);
  evaluated := EvaluateMonomials(G,mon);
  assert IsZero(&+[coeffs[i]*evaluated[i] : i in [1..#mon]]);
end for;
sane,Htrace,Htest := HilbertSeriesSanityCheck(M,1*ZF,[J]);
assert sane;
print "CHECK stored relation and full Hilbert series";
assert AlgebraicallyIndependent([G[2][1]^6,G[6][1]^2,G[2][1]*G[10][1]]);
print "CHECK algebraic independence";
skew := G[2][1]*G[6][1]^3-G[2][1]^2*G[6][1]*G[10][1]-8*G[20][1]+52*G[10][1]^2;
assert not IsZero(skew) and Swap(skew) eq (-1)*skew;
for weight in [2,6,10] do
  assert Swap(G[weight][1]) eq G[weight][1];
end for;

Mlo := GradedRingOfHMFs(F,20);
low := ConstructGeneratorsAndRelations(Mlo,1*ZF,10,12);
Glo := low[1];
Rlo := ConstructWeightedPolynomialRing(Glo);
for weight in [2,6,10] do
  for nu in FunDomainRepsUpToPrec(Mlo,bb,20) do
    assert Coefficient(G[weight][1],bb,nu : InFunDomain:=true)
        eq Coefficient(Glo[weight][1],bb,nu : InFunDomain:=true);
  end for;
end for;

// The minus parts vanish because the determinant-unit quotient is trivial.
// The Siegel normalization follows examples/igusa_invariants.m.
psi := AssociativeArray();
for weight in [4,6,10,12] do
  plus,minus := SiegelEisensteinPullback(Mlo,[weight,weight]);
  assert IsZero(minus);
  psi[weight] := plus;
end for;
chi10 := -43867/(2^12*3^5*5^2*7*53)*(psi[4]*psi[6]-psi[10]);
chi12 := 131*593/(2^13*3^7*5^3*7^2*337)*(3^2*7^2*psi[4]^3+2*5^3*psi[6]^2-691*psi[12]);
for i->form in [*psi[4],psi[6],chi10,chi12*] do
  bas,mon := CanonicalBasis(Glo,low[2],form);
  AAlo := CoefficientsMatrix(bas cat [form]);
  assert Rank(RowSubmatrix(AAlo,1,#bas)) eq Dimension(Parent(form));
  ok,sol := IsConsistent(RowSubmatrix(AAlo,1,#bas),RowSubmatrix(AAlo,#bas+1,1));
  assert ok;
  expected := Evaluate(pullbacks[i],[Rlo|Rlo.1,Rlo.2,Rlo.3,0]);
  assert &+[Rlo|sol[1][j]*mon[j] : j in [1..#bas]] eq expected;
end for;
// Mestre/Qsqrt3.m gives the conversion from Siegel to Igusa-Clebsch forms.
psi4c,psi6c,chi10c,chi12c := Explode([ev(p,[K|1,a,b,t]) : p in pullbacks]);
assert II eq [-24*chi12c/chi10c,4*psi4c,-8*psi6c/3-32*psi4c*chi12c/chi10c,-2^14*chi10c];
print "CHECK exact modular dictionary, component, determinant units, and swap";
assert #hashes eq 2 and &and[#h eq 64 : h in hashes];
for p in [K|a,b,II[1],II[4]] cat phiFF do
  assert p ne 0;
  assert not Numerator(p) in Jo and not Denominator(p) in Jo;
end for;
for p in [L|g,h,IEK[1],IEK[4],excludedEK,7776-2*j[1]*AA*r,1-4*k] cat psiFF do
  assert p ne 0;
end for;
print "CHECK chart excludes X2=0, a=0, b=0, I2=0, the source bad locus, and rational-inverse poles";
if assigned fixture_twist then
  twists := [StringToInteger(fixture_twist)];
  assert twists eq [2];
else
  twists := [1,2];
end if;
results := AssociativeArray(Integers());
for d in twists do
  JD := ideal<P|Z^2-d*B>;
  JE := ideal<Q|Q.3^2-d*f>;
  assert Numerator(ev(Q.3^2-d*f,phiFF)) in JD;
  assert Numerator(ev(P!Z^2-d*B,psiFF)) in JE;
  for i in [1..3] do
    delta := ev(psiFF[i],phiFF)-K.i;
    assert Numerator(delta) in JD and not Denominator(delta) in JD;
    delta := ev(phiFF[i],psiFF)-L.i;
    assert Numerator(delta) in JE and not Denominator(delta) in JE;
  end for;
  print "CHECK both rational compositions",d;
  deck := [K|a,b,(a^3-a*b+52*b^2)/4-t];
  assert ev(phiFF[1],deck) eq phiFF[1];
  assert ev(phiFF[2],deck) eq phiFF[2];
  assert ev(phiFF[3],deck) eq -phiFF[3];
  assert ev(Z^2-d*B,deck) eq Z^2-d*B;
  assert &or[IsOdd(e[2]) : e in Factorization(d*f)];
  assert d*B/ev(f,phiFF) eq d*(2^23*a^5/b)^2;
  assert IsSquarefree(d);
  assert d eq 1 or not IsSquare(Rationals()!d);
  if d eq 1 then
    results[d] := "PASS EK D=5 over Q";
  else
    results[d] := Sprintf("TWIST EK D=5 c=%o",d);
    assert results[d] eq "TWIST EK D=5 c=2";
    assert not "PASS" in results[d];
  end if;
end for;
if 2 in twists then print results[2]; end if;
if 1 in twists then print results[1]; end if;
