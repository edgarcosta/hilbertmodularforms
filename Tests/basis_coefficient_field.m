// Basis must retain the coefficient field, including when row reduction
// leaves only rational coefficients in a form over an extension.
procedure test_basis_coefficient_field()
  F := QuadraticField(5);
  ZF := Integers(F);
  M := GradedRingOfHMFs(F, 30);
  B := Basis(HMFSpace(M, 4*ZF, [2,2]));
  assert #B eq 3;
  L<a> := QuadraticField(2);
  f := ChangeCoefficientRing(B[1], L);
  g := ChangeCoefficientRing(B[2], L);

  for h in [f + a*g, a*f] do
    result := Basis([h, 2*h]);
    assert #result eq 1;
    assert CoefficientRing(result[1]) eq L;
    assert #LinearDependence(result cat [h]) eq 1;
  end for;
end procedure;

test_basis_coefficient_field();
