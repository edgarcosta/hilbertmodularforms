H<t> := FunctionField(Rationals());

procedure check_presentation(I, tau, weights, series)
  K, images, hs := SymmetricSubringPresentation(I, tau);
  P := Generic(K);
  assert not IsEmpty(images);
  assert Sort(VariableWeights(P)) eq Sort(weights);
  assert H!hs eq series;
  assert H!HilbertSeries(K) eq series;
  assert IsSymmetricSubringPresentation(I, tau, K, images);
  assert &and[Evaluate(f, images) in I : f in Basis(K)];
  assert &and[Evaluate(f, tau) - f in I : f in images];
end procedure;

// The identity fixes the whole polynomial ring.
procedure test_identity_action()
  R<x, y> := PolynomialRing(Rationals(), [2, 2]);
  check_presentation(ideal<R |>, [x, y], [2, 2], 1/(1 - t^2)^2);
end procedure;

test_identity_action();

// The action is read modulo the ideal: y^2 = x^2 there, so x alone generates.
procedure test_quotient()
  R<x, y> := PolynomialRing(Rationals(), [2, 2]);
  check_presentation(ideal<R | y^2 - x^2>, [x, -y], [2], 1/(1 - t^2));
end procedure;

test_quotient();

// Any representative of a graded map is accepted: modulo y, x + y is x.
procedure test_representatives_modulo_ideal()
  R<x, y> := PolynomialRing(Rationals(), [2, 4]);
  I := ideal<R | y>;
  P<a> := PolynomialRing(Rationals(), [2]);
  K := ideal<P |>;
  assert IsSymmetricSubringPresentation(I, [x + y, y], K, [x]);
  assert IsSymmetricSubringPresentation(I, [x, y], K, [x + y]);
  check_presentation(I, [x + y, y], [2], 1/(1 - t^2));
end procedure;

test_representatives_modulo_ideal();

// Negating both variables gives the quadratic Veronese ring, with one relation;
// verification rejects a kernel that misses it.
procedure test_sign_action()
  R<x, y> := PolynomialRing(Rationals(), [2, 2]);
  I := ideal<R |>;
  check_presentation(I, [-x, -y], [4, 4, 4], (1 - t^8)/(1 - t^4)^3);
  P<a, b, c> := PolynomialRing(Rationals(), [4, 4, 4]);
  assert IsSymmetricSubringPresentation(I, [-x, -y],
      ideal<P | b^2 - a*c>, [x^2, x*y, y^2]);
  assert not IsSymmetricSubringPresentation(I, [-x, -y],
      ideal<P |>, [x^2, x*y, y^2]);
end procedure;

test_sign_action();

// The involution z -> x^2 - z is not linear in the variables; z^2 is not invariant.
procedure test_nonlinear_action()
  R<x, z> := PolynomialRing(Rationals(), [2, 4]);
  I := ideal<R |>;
  check_presentation(I, [x, x^2 - z], [2, 8], 1/((1 - t^2)*(1 - t^8)));
  P<a, b> := PolynomialRing(Rationals(), [2, 8]);
  assert IsSymmetricSubringPresentation(I, [x, x^2 - z],
      ideal<P |>, [x, (z - x^2/2)^2]);
  assert not IsSymmetricSubringPresentation(I, [x, x^2 - z],
      ideal<P |>, [x, z^2]);
end procedure;

test_nonlinear_action();

// Swapping x and y, with the redundant generator z = x*y.
procedure test_swap_with_relation()
  R<x, y, z> := PolynomialRing(Rationals(), [2, 2, 4]);
  I := ideal<R | z - x*y>;
  check_presentation(I, [y, x, x*y], [2, 4], 1/((1 - t^2)*(1 - t^4)));
  P<a, b> := PolynomialRing(Rationals(), [2, 4]);
  assert IsSymmetricSubringPresentation(I, [y, x, x*y],
      ideal<P |>, [x + y, x*y]);
end procedure;

test_swap_with_relation();

// Both intrinsics reject a map that is not an involution, and a map that does not
// preserve the ideal.
procedure test_rejected_actions()
  R<x> := PolynomialRing(Rationals(), [2]);
  I := ideal<R |>;
  P<a> := PolynomialRing(Rationals(), [2]);
  assert not IsSymmetricSubringPresentation(I, [2*x], ideal<P |>, [x]);
  rejected := false;
  try
    _ := SymmetricSubringPresentation(I, [2*x]);
  catch e
    rejected := "graded involution" in e`Object;
  end try;
  assert rejected;

  R<x, y> := PolynomialRing(Rationals(), [2, 2]);
  I := ideal<R | x>;
  assert not IsSymmetricSubringPresentation(I, [y, x], ideal<P |>, [y]);
  rejected := false;
  try
    _ := SymmetricSubringPresentation(I, [y, x]);
  catch e
    rejected := "graded involution" in e`Object;
  end try;
  assert rejected;
end procedure;

test_rejected_actions();

// Verification rejects images that generate a proper subring of the fixed ring,
// and images that are not invariant.
procedure test_invalid_images()
  R<x> := PolynomialRing(Rationals(), [2]);
  I := ideal<R |>;
  P<a> := PolynomialRing(Rationals(), [4]);
  assert not IsSymmetricSubringPresentation(I, [x], ideal<P |>, [x^2]);
  P<a> := PolynomialRing(Rationals(), [2]);
  assert not IsSymmetricSubringPresentation(I, [-x], ideal<P |>, [x]);
end procedure;

test_invalid_images();
