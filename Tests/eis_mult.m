// Tests that the product of E(1,chi) * E(1, chi^-1) 
// has rational coefficients. 
// TODO abhijitm - the Eisenstein basis code is still broken
// I think, but once it's fixed this test should also verify
// that the product is also an Eisenstein series

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
assert CoefficientRing(f) eq Rationals();

// M22 := HMFSpace(M, N, [2,2]);
// E22 := EisensteinBasis(M22);
// assert #LinearDependence(Append(E22, f)) eq 1;

