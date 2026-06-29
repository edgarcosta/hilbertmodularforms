procedure test_X011_equation()
  Q := Rationals();
  R<E2, f2, E4> := PolynomialRing(Q, [2,2,4]);
  PR := ProjectiveSpace(R);
  R8 := E2^4 + 240*E2^3*f2+2592*E2^2*f2^2+8640*E2*f2^3+9216*f2^4-122*E2^2*E4-240*E2*f2*E4+288*f2^2*E4+121*E4^2;
  S := Scheme(PR, R8);
  M := MonomialsOfWeightedDegree(R, 4);
  PN<[z]> := ProjectiveSpace(Q, #M - 1);
  // construct the Veronese embedding into regular projective space
  // so that Magma will be able to do something with it
  nu := map< PR -> PN | [m : m in M] >;
  C := Curve(S);
  C_prime := nu(C);
  pt := C_prime![1,0,0,1];
  E := EllipticCurve(C_prime, pt);
  assert Conductor(E) eq 11;
  X011 := X0NQuotient(11, []);
  assert IsIsomorphic(X011, E);
end procedure;

test_X011_equation();
