load "config.m";

F := QuadraticField(23);
ZF := Integers(F);
// N := 1*ZF;
N := 3*ZF;
prec := 100;
M := HMFSpace(F, N, prec);

k := [4,4];

// X := DirichletGroup(N);
X := HeckeCharacterGroup(N);

triv := X!1;
eta := Random(X);
psi := Random(X);

// intrinsic EisensteinSeries(M::ModFrmHilD, eta::GrpHeckeElt, psi::GrpHeckeElt, k::SeqEnum[RngIntElt]) -> ModFrmHilDElt

Cl := NarrowClassGroup(M);
mp := NarrowClassGroupMap(M);
if #Cl eq 1 then
  tt := mp(Cl.1);
else
  tt := mp(Cl.1);
  // error "not implemented for narrow class number > 1.";
end if;
X := Parent(eta);
assert X eq Parent(psi);
K := X`TargetRing; // where the character values live
n := Degree(BaseField(M));
assert #SequenceToSet(k) eq 1; // parallel weight
assert k[1] ge 2; // we can remove this later
nn := Level(M);
aa := Conductor(eta);
bb := Conductor(psi);
assert nn subset aa;
assert nn subset bb;
Haa := HeckeCharacterGroup(aa);
Hbb := HeckeCharacterGroup(bb);
ideals := Ideals(M);
coeffs := [ K!0 : i in [1..#ideals]];
// constant term, in general this will be a list of length #Cl
if aa eq ideal<Order(aa)|1> then
  prim := AssociatedPrimitiveCharacter(psi*eta^(-1));
  prec := 50;
  CC := ComplexField(prec);
  Lf := LSeries(prim : Precision := prec);
  Lvalue := CC!Evaluate(Lf, 1-k[1]);
  Lvalue_recognized := RecognizeOverK(Lvalue, K, InfinitePlaces(K)[1], false);
  coeffs[1] := 2^(-n)*(eta^(-1))(tt)*Lvalue_recognized;
else
  coeffs[1] := 0;
end if;
// other terms
for i := 2 to #ideals do
  mm := ideals[i];
  sum := 0;
  for rr in Divisors(mm) do
    sum +:= eta(mm/rr)*psi(rr)*Norm(rr^(k[1]-1));
  end for;
  coeffs[i] := sum;
end for;
