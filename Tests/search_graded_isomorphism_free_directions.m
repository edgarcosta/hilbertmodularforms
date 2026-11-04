// Diagonal pins leave torus parameters or free shifts in these rings.
// Rational slices must recover maps without advancing the caller's random state.
procedure test_round_trip(name, I, phi0)
  R := Generic(I);
  h := hom<R -> R | phi0>;
  J := ideal<R | [h(g) : g in Basis(I)]>;
  assert VerifyGradedIsomorphism(I, J, phi0, GradedInverseImages(R, phi0));
  seed, step := GetSeed();
  found, Phi, Psi := SearchGradedIsomorphism(I, J : Candidates := [1], MaxAttempts := 1);
  error if not found, name cat ": no map found";
  nextSeed, nextStep := GetSeed();
  assert <nextSeed, nextStep> eq <seed, step>;
  assert VerifyGradedIsomorphism(I, J, Phi, Psi);
end procedure;

// A nonsplit torus exercises rational specialization beyond a fixed identity map.
procedure test_nonsplit_torus()
  R<u, v, w> := PolynomialRing(Rationals(), [2, 4, 4]);
  I := ideal<R | v^2 - 2*w^2 - u^4>;
  test_round_trip("torus", I, [R | u, v + u^2, 2*w + u^2]);
end procedure;

test_nonsplit_torus();

// Fixing the determinant unknowns to small values misses this rational torus map.
procedure test_torus_determinant()
  T<x, y, z, t> := PolynomialRing(Rationals(), [2, 2, 6, 6]);
  I := ideal<T | z*t - x^3*y^3>;
  test_round_trip("torus with determinant 3", I, [T | x + y, y, 3*z + x^3, t]);
end procedure;

test_torus_determinant();

// c is in no relation, so its scaling and its shifts by weight-8 monomials in a, b stay free.
procedure test_free_shifts()
  S<a, b, c> := PolynomialRing(Rationals(), [2, 4, 8]);
  I := ideal<S | b^2>;
  test_round_trip("free shifts and top scaling", I, [S | a, b + a^2, c + a^2*b + a^4]);
end procedure;

test_free_shifts();

// The weight-6 determinant on this D=13 torus is a sixth power times 3.
procedure test_d13_torus_determinant()
  U<a, u, e, c, z> := PolynomialRing(Rationals(), [2, 2, 2, 6, 6]);
  K := ideal<U | [
    u^3*e^3 + a*u^2*c - u^3*c - a*u*e*c + 1/2*u^2*e*c
      + a*e^2*c - 1/2*u*e^2*c - 1/2*e^3*c + c*z,
    a^2*c - 2*a*u*c + u^2*c - a*e*c + u*e*c + 1/4*e^2*c
      - u^2*z - 2*u*e*z - e^2*z,
    a*u^3 + 1/2*u^3*e + a*c - u*c - 1/2*e*c + u*z + e*z,
    u^4 + u^3*e + a*c - u*c - 1/2*e*c]>;
  test_round_trip("D13 torus with determinant 3", K, [U | a, u, e, 3*c, z]);
end procedure;

test_d13_torus_determinant();
