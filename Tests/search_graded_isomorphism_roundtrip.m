// SearchGradedIsomorphism (Verification/IsIsomorphic.m) POSITIVE round-trips at the
// ideal level, using stored canonical rings loaded via LoadStoredCanonicalRing (no HMF
// recomputation).  For each stored ring we apply a KNOWN graded automorphism phi0 whose
// diagonal scalings lie in the finder's default candidate set (signed powers of two), so
// the isomorphism is inside the finder's search space, producing J = phi0(I).  We then
// assert SearchGradedIsomorphism(I, J) succeeds and the returned map is certified by the
// deterministic VerifyGradedIsomorphism.  The recovered map need NOT equal phi0: any map
// the certifier accepts is a valid witness.
//
// Rings, in increasing complexity (all fast, single narrow-class-component files):
//   D=13                   [2, 4, 6, 6, 8] -- equal-weight block (two weight-6), 2 relations
//   D=8                    [2, 4, 6, 14]
//   D=5                    [2, 6, 10, 20]
// The automorphisms combine in-scope diagonal scalings, a permutation of the equal-weight
// generators, and lower-order polynomial mixing (which the finder resolves by linear
// algebra rather than search).  Resources: ~6s CPU (dominated by the D=5 search).
//
// (The D=8 second component [2,2,4,10] is deliberately omitted: its single degree-10
// relation has huge coefficients and its free weight-2 block makes the Variety solve run
// for minutes, too slow for CI.  The equal-weight requirement is met by the D=13 swap.)
printf "SearchGradedIsomorphism positive round-trips (stored canonical rings)...\n";
t0 := Cputime(); walltime := Time();

// Given a loaded ideal I and a graded automorphism phi0 (images of the source variables,
// polynomials in Generic(I)), form J = phi0(I) in the SAME ring and assert the finder
// recovers a certified map.  phi0 MUST be built from Generic(I) itself: each
// LoadStoredCanonicalRing call builds a fresh ring, so images must use this I's variables.
procedure RoundTrip(name, I, phi0)
  R := Generic(I);
  assert &and[Parent(p) cmpeq R : p in phi0];
  h := hom< R -> R | phi0 >;
  J := ideal< R | [h(f) : f in Basis(I)] >;

  ts := Cputime();
  found, Phi, Psi := SearchGradedIsomorphism(I, J);
  assert found;
  assert VerifyGradedIsomorphism(I, J, Phi, Psi);
  printf "  %o: found and certified [%o s]\n", name, Cputime(ts);
end procedure;

// ---- D=13 [2, 4, 6, 6, 8]: diagonal (top weight determined by the relations). ----
procedure test_D13_diagonal()
  I13 := LoadStoredCanonicalRing("2.2.13.1-1.1");
  R13 := Generic(I13);
  RoundTrip("D=13 diagonal", I13,
    [R13 | 2*R13.1, 4*R13.2, -2*R13.3, 8*R13.4, 16*R13.5]);
end procedure;

// ---- D=13 again: PERMUTE the two weight-6 generators, plus scalings.  This exercises the
//      equal-weight free block that Variety must resolve (a swap is not diagonal). ----
procedure test_D13_weight6_swap()
  I13 := LoadStoredCanonicalRing("2.2.13.1-1.1");
  R13 := Generic(I13);
  RoundTrip("D=13 weight-6 swap", I13,
    [R13 | 2*R13.1, 4*R13.2, R13.4, R13.3, 16*R13.5]);
end procedure;

// ---- D=8 [2, 4, 6, 14]: diagonal scalings PLUS lower-order polynomial mixing, which the
//      finder resolves linearly (not by search). ----
procedure test_D8_diagonal_mixing()
  I8 := LoadStoredCanonicalRing("2.2.8.1-1.1");
  R8 := Generic(I8);
  b2 := R8.1; b4 := R8.2; b6 := R8.3; b14 := R8.4;
  RoundTrip("D=8 diagonal + mixing", I8,
    [R8 | 2*b2,
          4*b4 + b2^2,
          8*b6 + b2*b4,
          16*b14 + b2^7 + b4^2*b6]);
end procedure;

// ---- D=5 [2, 6, 10, 20]: diagonal scalings (heaviest of the fast rings). ----
procedure test_D5_diagonal()
  I5 := LoadStoredCanonicalRing("2.2.5.1-1.1");
  R5 := Generic(I5);
  RoundTrip("D=5 diagonal", I5,
    [R5 | -2*R5.1, 4*R5.2, 8*R5.3, 16*R5.4]);
end procedure;

test_D13_diagonal();
test_D13_weight6_swap();
test_D8_diagonal_mixing();
test_D5_diagonal();

printf "PASSED (CPU: %os, Wall: %os, Mem: %oMB)\n", Cputime(t0), Time(walltime), GetMemoryUsage() div (1024^2);
