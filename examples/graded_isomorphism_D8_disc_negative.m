// No-false-positive check for SearchGradedIsomorphism (Verification/IsIsomorphic.m) on the
// D=8 canonical ring against the WRONG-SIGN discriminant relation.  The literature model of
// the Q(sqrt(8)) canonical ring in weights [2,4,6,14] is
//     27*X14^2 - disc,
// and it IS isomorphic to ours (see examples/graded_isomorphism_D5_D8_D13.m).  Flipping the
// sign to 27*X14^2 + disc gives a ring with the SAME Hilbert series but no graded
// isomorphism over Q to ours (matching the two would need sqrt(-1) in a scaling).  Since the
// Hilbert series agree there is no cheap obstruction, so the finder runs its full exhaustive
// search over the default candidate diagonals and must terminate with "false".
//
// This is an exhaustive Variety sweep over the candidate set (roughly a minute), the heaviest
// of the CI graded-isomorphism checks.
printf "SearchGradedIsomorphism D=8 +disc no-false-positive...\n";
t0 := Cputime(); walltime := Time();
procedure test_d8_plus_disc_no_false_positive()
  Q := Rationals();

  R8<X2,X4,X6,X14> := PolynomialRing(Q, [2,4,6,14]);
  Fours := X2^2*X4^6 + 276*X2*X4^5*X6 + 80*X2^2*X4^3*X6^2 + 1124*X4^4*X6^2
    + 740*X2*X4^2*X6^3 + X2^2*X6^4 + 1728*X4*X6^4
    - 2*X2*X4^3*X14 - X2^2*X4*X6*X14 - 20*X4^2*X6*X14 - 2*X2*X6^2*X14 + X14^2;
  disc := (X4*(X6-4*X2*X4))*X6*(-4*(X2^2+12*X4)^3 + (27*X6+2*X2^3-72*X2*X4)^2);
  SFplus := 27*X14^2 + disc;   // WRONG SIGN: the correct literature relation is 27*X14^2 - disc.

  I := ideal< R8 | Fours >;
  Jplus := ideal< R8 | SFplus >;

  // The obstruction is arithmetic, not combinatorial: the Hilbert series coincide.
  assert HilbertSeries(I) eq HilbertSeries(Jplus);

  found, _, _ := SearchGradedIsomorphism(I, Jplus);
  assert not found;
end procedure;

test_d8_plus_disc_no_false_positive();

printf "PASSED (CPU: %os, Wall: %os, Mem: %oMB)\n", Cputime(t0), Time(walltime), GetMemoryUsage() div (1024^2);
