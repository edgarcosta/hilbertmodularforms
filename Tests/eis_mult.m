// Tests that the product of E(1,chi) * E(1, chi^-1) 
// has rational coefficients. 

F := QuadraticField(5);
ZF := Integers(F);
prec := 10;
M := GradedRingOfHMFs(F, prec);
N := 14*ZF;

H := HeckeCharacterGroup(N, [1,2]);
chi := H.1;

H_prim := HeckeCharacterGroup(7*ZF, [1,2]);
chi_prim := (H_prim).1;

triv_char := HeckeCharacterGroup(1*ZF, [1, 2]).0;

MEis := HMFSpace(M, N, [1,1], chi^-1);
MEisinv := HMFSpace(M, N, [1,1], chi);
E := EisensteinSeries(MEis, chi_prim^-1, triv_char);
Einv := EisensteinSeries(MEisinv, chi_prim, triv_char);

f := E * Einv;
f := ChangeCoefficientRing(f, Rationals());
assert CoefficientRing(f) eq Rationals();

M22 := HMFSpace(M, N, [2,2]);
B22 := Basis(M22);
assert #LinearDependence(Append(B22, f)) eq 1;

