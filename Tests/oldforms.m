function test(F, N, k, true_old_dim)
  // F : FldNum - A number field
  // N : RngOrdIdl - A level
  // k : SeqEnum[RngIntElt] - A weight
  // true_old_dim : int - The dimension of the 
  //     space of old cusp forms for this F, N, k
  prec := 250;
  bound := 50;
  M := GradedRingOfHMFs(F, prec);
  Mk := HMFSpace(M, N, k);

  new_basis := NewCuspFormBasis(Mk);
  old_basis := OldCuspFormBasis(Mk);

  assert #old_basis eq true_old_dim;

  // The union of new and old bases should be linearly
  // dependent

  assert #LinearDependence(new_basis cat old_basis) eq 0;

  // Check that the claimed old basis vectors
  // are Hecke operators for a prime not dividing
  // the level.

  pp := PrimesUpTo(bound, F:coprime_to := N)[1];
  for f in old_basis do
    g := HeckeOperator(f, pp);
    assert #LinearDependence([f, g]) eq 1;
  end for;
  return "";
end function;


k := [2,2];

F := QuadraticField(5);
N := 12*Integers(F);
true_old_dim := 2;
test(F, N, k, true_old_dim);

F := QuadraticField(3);
N := 6*Integers(F);
true_old_dim := 3;
test(F, N, k, true_old_dim);
