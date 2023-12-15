printf "Testing E_2 over Q(sqrt(13)) and that E2^2 matches..."; //use printf with no \n
// Create the graded ring
F:=QuadraticField(13);
ZF := Integers(F);
prec:=125;
M:=GradedRingOfHMFs(F, prec);
// Create the space of parallel weight [4,4] and level 1
ZF:=Integers(F);
N:=1*ZF;
M2 := HMFSpace(M, [2,2]);
X := Parent(Character(M2));
triv := X!1;
eta := X!1;
psi := X!1;

E2 := EisensteinSeries(M2, eta, psi);

assert [Coefficients(E2)[1*ZF][elt] : elt in FunDomainRepsUpToNorm(M, 1*ZF, 30)] eq
[ 1, 24, 96, 96, 120, 384, 312, 312, 480, 480, 336, 504, 432, 432, 576, 576, 624, 960, 1248, 960, 1248, 720, 720 ];

E2pow2 := E2^2;
assert [Coefficients(E2pow2)[1*ZF][elt] : elt in FunDomainRepsUpToNorm(M, 1*ZF, 30)] eq
[ 1, 48, 192, 192, 816, 6528, 5232, 5232, 14784, 14784, 20256, 33840, 38880, 38880, 107136, 107136, 136032, 171264, 176448, 171264, 176448, 196128, 196128 ];

assert E2pow2/E2 eq E2;


h:=1/Coefficient(E2, 1*ZF)*E2;
hecke_h := HeckeOperator(h, 2*ZF);
assert IsZero(hecke_h - Coefficient(h, 2*ZF)*h);


M4 := HMFSpace(M, [4,4]);
time B4 := Basis(M4 : ViaTraceForm:=false);
assert #B4 eq 2;
assert {[Coefficients(b)[1*ZF][elt] : elt in FunDomainRepsUpToNorm(M, 1*ZF, 20)]:  b in B4 } eq
{
[ 1, 240/29, 6720/29, 6720/29, 15600/29, 188160/29, 181680/29, 181680/29, 436800/29, 436800/29, 527520/29, 998640/29, 1179360/29, 1179360/29 ],
[ 0, 1, -1, -1, 7, 1, -26, -26, -7, -7, 52, -15, -45, -45 ]
};
assert LinearDependence([E2pow2] cat B4) eq [ [ 29, -29, -1152 ] ];
time TB4 := Basis(M4 : ViaTraceForm:=true);
assert #LinearDependence(TB4 cat B4) eq #B4;
