printf "Testing creation of E_2 over Q(sqrt(13))...";
// Create the graded ring
F:=QuadraticField(13);
ZF := Integers(F);
prec:=10;
M:=GradedRingOfHMFs(F, prec);
// Create the space of parallel weight [4,4] and level 1
ZF:=Integers(F);
N:=1*ZF;
M2 := HMFSpace(M, [2,2]);
X := HeckeCharacterGroup(N);
triv := X!1;
eta := X!1;
psi := X!1;

E2 := EisensteinSeries(M2, eta, psi);

assert [Coefficients(E2)[1*ZF][elt] : elt in ShintaniRepsUpToTrace(M, 1*ZF, 3)] eq
[ 1, 24, 96, 96, 120, 312, 480, 336, 480, 312, 384, 432, 576, 1248, 720, 720, 1248, 576, 432 ];
printf "Success!\n";



printf "E2^2 has the right coefficients...";
E2pow2 := E2^2;
assert [Coefficients(E2pow2)[1*ZF][elt] : elt in ShintaniRepsUpToTrace(M, 1*ZF, 3)] eq
[ 1, 48, 192, 192, 816, 5232, 14784, 20256, 14784, 5232, 6528, 38880, 107136, 176448, 196128, 196128, 176448, 107136, 38880 ];
printf "Success!\n";

printf "E2^2/E2 = E2...";
assert E2pow2/E2 eq E2;
printf "Success!\n";


printf "E2 is an eigenvalue for T_{2*ZF}...";
h:=1/Coefficient(E2, 1*ZF)*E2;
hecke_h := HeckeOperator(h, 2*ZF);
assert IsZero(hecke_h - Coefficient(h, 2*ZF)*h);
printf "Success!\n";


printf "Computing the Basis for M_4...";
M4 := HMFSpace(M, [4,4]);
B4:=Basis(M4);
assert #B4 eq 2;
assert {[Coefficients(b)[1*ZF][elt] : elt in ShintaniRepsUpToTrace(M, 1*ZF, 2)]:  b in B4 } eq
{
[ 1, 240/29, 6720/29, 6720/29, 15600/29, 181680/29, 436800/29, 527520/29, 436800/29, 181680/29 ],
[ 0, 1, -1, -1, 7, -26, -7, 52, -7, -26 ]
};
printf "Success!\n";

printf "E2^2 in M_4...";
assert LinearDependence([E2pow2] cat B4) eq [ [ 29, -29, -1152 ] ];
printf "Success!\n";
