// An extension-field line in the Hecke kernel is stable even when no
// nonzero form on that line has rational coefficients.
procedure test_hecke_stable_extension_field_kernel()
  F := QuadraticField(5);
  ZF := Integers(F);
  M := GradedRingOfHMFs(F, 120);
  pp := 2*ZF;
  B := Basis(HMFSpace(M, 8*ZF, [2,2]));
  TB := [HeckeOperator(f, pp) : f in B];
  relations := LinearDependence(TB);
  assert #relations eq 2;
  K := [&+[r[i]*B[i] : i in [1..#B]] : r in relations];
  assert #LinearDependence(K) eq 0;
  assert &and[IsZero(HeckeOperator(k, pp)) : k in K];
  L<a> := QuadraticField(2);
  f := ChangeCoefficientRing(K[1], L) + a*ChangeCoefficientRing(K[2], L);
  assert not IsZero(f);
  assert IsZero(HeckeOperator(f, pp));

  W := HeckeStableSubspace([f], pp);
  assert #W eq 1;
  assert CoefficientRing(W[1]) eq L;
  assert #LinearDependence(W cat [f]) eq 1;
end procedure;

test_hecke_stable_extension_field_kernel();
