// S. Mayer, "Hilbert Modular Forms for the fields Q(sqrt5), Q(sqrt13)
// and Q(sqrt17)", thesis (2007), revised edition (2008), Thm 6.5.1, pp.134-135.
// LitData certifies the full even, trivial-multiplier subring of the quotient by R3 and R9.
//
// eval-loaded: `LitData := eval (Read(<this file>) cat "return LitData;");`
// Call with rings S, R of weights [2,4,4,6,6,6,8], where R = Generic(J):
// `I, PhiImages, PsiImages, citation := LitData(S, R);`
LitData := function(Rsrc, Rtgt)
  weights := [2,4,4,6,6,6,8];
  assert VariableWeights(Rsrc) eq weights;
  assert VariableWeights(Rtgt) eq weights;

  // Weights are doubled; [e,c,b,a,d] = [Psi17,eta2,Psi2,Psi1,E2].
  // Table 6.5 (p.135) gives the exponents; Cor. 5.2.2 (p.120) gives modulus 8.
  P<e,c,b,a,d> := PolynomialRing(Rationals(), [9,3,3,1,4], "lex");
  multiplierExponents := [5,1,5,1,0];
  R3 := c^2 - 64*b^2 - 16*a^2*d;
  R9 := e^2 - b^2*d^3 + 216*b^5*c
      + 256*a^18 + 176*a^12*b*c + 2671/4096*a^6*c^4
      - 103/8*a^4*d^2*b*c + 87/16*a^10*d^2
      + 99/128*a^2*d*b*c^3 - 1387/128*a^8*d*c^2;
  fullIdeal := ideal<P | R3,R9>;
  assert IsHomogeneous(fullIdeal);
  multiplierResidue := func<m |
    (&+[Exponents(m)[i]*multiplierExponents[i] : i in [1..5]]) mod 8>;
  assert &and[{multiplierResidue(m) : m in Monomials(f)} eq {2} : f in [R3,R9]];

  // Thm 6.5.1 and Table 6.5 use opposite signs for eta2: with Table 6.5's
  // diagonal values, R3 restricts to 0 but R9 to -3456*u^6, u = eta^6.
  // The ambient graded automorphism c -> -c fixes R3 and gives an
  // isomorphic presentation; the literal printed coefficients are retained.
  invariantMonomial := func<m | WeightedDegree(m) mod 4 eq 0 and
    multiplierResidue(m) eq 0>;
  invariantGenerators := [d,a^8,c*b*a^2,c*b^3,b^2*a^6,e*a^3,e*b^2*a];
  assert &and[invariantMonomial(m) : m in invariantGenerators];
  assert [Integers()!(WeightedDegree(m)/2) : m in invariantGenerators] eq weights;
  x := [Rsrc.i : i in [1..Rank(Rsrc)]];
  relations := [ Rsrc |
  x[1]^3*x[3]*x[4] - 99/2*x[1]*x[3]^2*x[4] - 216*x[3]*x[4]^2 + 16*x[1]^3*x[2]*x[5] -
    4096*x[1]*x[2]^2*x[5] + 8*x[1]^3*x[3]*x[5] - 2816*x[1]*x[2]*x[3]*x[5] - 642*x[1]*x[3]^2*x[5] +
    32*x[1]^2*x[4]*x[5] - 2671*x[3]*x[4]*x[5] + 64*x[1]^2*x[5]^2 - 16384*x[2]*x[5]^2 -
    11264*x[3]*x[5]^2 - 16*x[1]*x[6]*x[7] - 64*x[7]^2,
  x[1]^3*x[3]^2 - 216*x[3]^2*x[4] - 16*x[1]^4*x[5] + 64*x[1]^2*x[2]*x[5] - 16384*x[2]^2*x[5] +
    32*x[1]^2*x[3]*x[5] - 11264*x[2]*x[3]*x[5] - 2671*x[3]^2*x[5] + 288*x[1]*x[4]*x[5] +
    1648*x[1]*x[5]^2 - 64*x[6]*x[7],
  x[3]^2*x[6] - 16*x[1]*x[2]*x[7] - 64*x[5]*x[7],
  x[1]^2*x[2]^2 - 256*x[2]^3 + 1/2*x[1]^2*x[2]*x[3] - 176*x[2]^2*x[3] + x[1]^3*x[5] -
    642*x[1]*x[2]*x[5] - 99/2*x[1]*x[3]*x[5] - 216*x[4]*x[5] - 2671*x[5]^2 - x[6]^2,
  x[2]*x[3]^2 - 16*x[1]*x[2]*x[5] - 64*x[5]^2,
  x[3]^3 - 16*x[1]*x[3]*x[5] - 64*x[4]*x[5],
  x[4]*x[6] - x[3]*x[7],
  x[5]*x[6] - x[2]*x[7],
  x[2]*x[4] - x[3]*x[5]
  ];
  I := ideal<Rsrc | relations>;
  assert #relations eq 9;
  assert IsHomogeneous(I);
  assert &and[Evaluate(f, invariantGenerators) in fullIdeal : f in relations];

  // Leading monomials e^2,c^2 give a free Q[a,b,d]-module on 1,c,e,ce.
  // Reducing powers of a,b modulo 8 gives a basis over Q[a^8,b^8,d].
  assert {LeadingMonomial(f) : f in GroebnerBasis(fullIdeal)} eq {e^2,c^2};
  moduleBasis := [a^i*b^j*c^k*e^l : i,j in [0..7], k,l in [0..1] |
    invariantMonomial(a^i*b^j*c^k*e^l)];
  assert #moduleBasis eq 16;
  a4b4 := (x[3]^2 - 16*x[1]*x[5])/64;
  a2b6 := (x[3]*x[4] - 16*x[1]*a4b4)/64;
  b8 := (x[4]^2 - 16*x[1]*a2b6)/64;
  moduleImages := [ Rsrc |
    1, x[4], x[7], x[4]*x[7], x[3], a2b6, x[6], x[4]*x[6],
    a4b4, x[4]*a4b4, x[3]*x[6], a2b6*x[6], x[5], x[4]*x[5],
    a4b4*x[6], x[4]*a4b4*x[6]
  ];
  assert #moduleImages eq #moduleBasis;
  assert {NormalForm(Evaluate(f, invariantGenerators), fullIdeal) : f in moduleImages}
    eq Seqset(moduleBasis);
  assert Evaluate(b8, invariantGenerators)-b^8 in fullIdeal;

  // Generation gives a surjection onto the invariant subring; equal Hilbert
  // series certify that the nine relations are its entire kernel.
  H := HilbertSeries(I);
  z := Parent(H).1;
  invariantHilbert := (&+[z^(Integers()!(WeightedDegree(m)/2)) : m in moduleBasis]) /
    ((1-z^4)*(1-z^12)*(1-z^2));
  assert H eq invariantHilbert;

  x := [Rtgt.i : i in [1..Rank(Rtgt)]];
  PhiImages := [ Rtgt |
  x[1],
  x[2],
  -4*x[2] + 4*x[3],
  4*x[5] - 4*x[6],
  x[6],
  -x[1]*x[3] + 2*x[4] - 4*x[5] - x[6],
  -1/4*x[2]^2 - 3/2*x[2]*x[3] + 15/4*x[3]^2 + x[1]*x[5] + 1/4*x[1]*x[6] - 2*x[7]
  ];
  x := [Rsrc.i : i in [1..Rank(Rsrc)]];
  PsiImages := [ Rsrc |
  x[1],
  x[2],
  x[2] + 1/4*x[3],
  1/2*x[1]*x[2] + 1/8*x[1]*x[3] + 1/2*x[4] + 5/2*x[5] + 1/2*x[6],
  1/4*x[4] + x[5],
  x[5],
  x[2]^2 + 3/4*x[2]*x[3] + 15/128*x[3]^2 + 1/8*x[1]*x[4] + 5/8*x[1]*x[5] - 1/2*x[7]
  ];
  citation := "Mayer, thesis (2007, revised 2008), Thm 6.5.1 (literal presentation)";
  return I, PhiImages, PsiImages, citation;
end function;
return LitData;
