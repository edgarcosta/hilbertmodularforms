// Diagonal pins leave torus parameters or free shifts in these rings.
// Rational slices must recover maps without advancing the caller's random state.
printf "SearchGradedIsomorphism with free automorphism parameters...\n";
SetNthreads(1);
Q := Rationals();

procedure RoundTrip(name, I, phi0)
  R := Generic(I);
  h := hom< R -> R | phi0 >;
  J := ideal< R | [h(g) : g in Basis(I)] >;
  assert VerifyGradedIsomorphism(I, J, phi0, GradedInverseImages(R, phi0));
  seed, step := GetSeed();
  found, Phi, Psi := SearchGradedIsomorphism(I, J : Candidates := [1], MaxAttempts := 1);
  assert found;
  nextSeed, nextStep := GetSeed();
  assert <nextSeed, nextStep> eq <seed, step>;
  assert VerifyGradedIsomorphism(I, J, Phi, Psi);
  printf "  %o: found and certified\n", name;
end procedure;

// A nonsplit torus exercises rational specialization beyond a fixed identity map.
R<u, v, w> := PolynomialRing(Q, [2, 4, 4]);
I := ideal< R | v^2 - 2*w^2 - u^4 >;
RoundTrip("torus", I, [R | u, v + u^2, 2*w + u^2]);

// Fixing the determinant unknowns to small values misses this rational torus map.
T<x, y, z, t> := PolynomialRing(Q, [2, 2, 6, 6]);
I := ideal< T | z*t - x^3*y^3 >;
RoundTrip("torus with determinant 3", I, [T | x + y, y, 3*z + x^3, t]);

S<a, b, c> := PolynomialRing(Q, [2, 4, 8]);
I := ideal< S | b^2 >;
RoundTrip("free shifts and top scaling", I, [S | a, b + a^2, c + a^2*b + a^4]);

// The weight-6 determinant on this D=13 torus is a sixth power times 3.
U<a, u, e, c, z> := PolynomialRing(Q, [2, 2, 2, 6, 6]);
K := ideal< U | [
  u^3*e^3 + a*u^2*c - u^3*c - a*u*e*c + 1/2*u^2*e*c
    + a*e^2*c - 1/2*u*e^2*c - 1/2*e^3*c + c*z,
  a^2*c - 2*a*u*c + u^2*c - a*e*c + u*e*c + 1/4*e^2*c
    - u^2*z - 2*u*e*z - e^2*z,
  a*u^3 + 1/2*u^3*e + a*c - u*c - 1/2*e*c + u*z + e*z,
  u^4 + u^3*e + a*c - u*c - 1/2*e*c ] >;
RoundTrip("D13 torus with determinant 3", K, [U | a, u, e, 3*c, z]);

printf "free-directions search test passed.\n";
