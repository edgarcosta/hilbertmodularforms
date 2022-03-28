printf "Testing the computation of the Canonical ring for Q(sqrt(5))...";

F<nu> := QuadraticField(5);
ZF := Integers(F);
N := ideal<ZF|[1]>;
prec := 10;
R := GradedRingOfHMFs(F, prec);
B := AssociativeArray();
M := AssociativeArray();
for k:=2 to 10 by 2 do
    M[k] := HMFSpace(R, [k, k]);
    B[k] := Basis(M[k]);
end for;


E2 := B[2][1];
E4 := B[4][1];

// E2 generate everything at weight 4

assert E2^2 eq E4;

// E2, E6 generate everything at weight 6
assert #B[6] eq 2;
E6 := B[6][1];
cusp_forms6 := B[6][2];
f := E6 - E2^3;
f_normalized := (1/Coefficient(f, 1*ZF))*f;
assert f_normalized eq cusp_forms6;

// E2, E6 generate everything at weight 8
assert #B[8] eq 2;
E8 := B[8][1];

assert 536 * E2 * E6 -  175 * E2^4  eq  361 * E8;

cusp_forms8 := B[8][2];

g := E8- E2^4;
g_normalized := (1/Coefficient(g, 1*ZF))*g;
assert g_normalized eq cusp_forms8;

// E2, E6, E10 generate everything at weight 8
assert #B[10] eq 3;
E10 := B[10][1];

mon := MonomialsOfWeightedDegree([[2,6,10]],[10]);
Es := [* E2, E6, E10 *];
Epowers := [ Product([* Es[i]^(Integers() ! m[i]) : i in [1..#Es] *]) : m in mon ];

//E10 is linear independent from the rest
assert Rank(CoefficientsMatrix(Epowers)) eq #Epowers;
//the cusp forms can be written with E2, E6 and E10
assert Rank(CoefficientsMatrix(Epowers cat B[10])) eq #Epowers;


E20 := EisensteinBasis(HMFSpace(R, [k, k]) where k:=20);
mon := MonomialsOfWeightedDegree([[2,6,10]],[20]);
Epowers := [ Product([* Es[i]^(Integers() ! m[i]) : i in [1..#Es] *]) : m in mon ];
//the cusp forms can be written with E2, E6 and E10
assert not IsNull(LinearDependence(E20 cat Epowers));
return true;


