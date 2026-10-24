// F. Hirzebruch, "The ring of Hilbert modular forms for real quadratic fields
// of small discriminant", LNM 627 (1977), pp.305-310.
//
// M(Gamma0((sqrt5))) = M(Gamma(sqrt5))^D5.
// The complex Gamma(sqrt5) ring is C[A0,A1,A2,c]/(c^2-C), weights (1,1,1,5).
// We choose the rational model c^2 = 5*C, obtained by replacing c by sqrt(5)*c.
// Its even D5 invariants match Verification/CanonicalRingEquations/2.2.5.1-5.1-gl-0.m.
LitData := function(Rsrc, Rtgt)
  weights := [2, 2, 6, 10, 10];
  assert VariableWeights(Rsrc) eq weights;
  assert VariableWeights(Rtgt) eq weights;
  P<x,y,z,c> := PolynomialRing(Rationals(), [1, 1, 1, 5]);
  C := 320*x^6*y^2*z^2-160*x^4*y^3*z^3+20*x^2*y^4*z^4+6*y^5*z^5
    -4*x*(y^5+z^5)*(32*x^4-20*x^2*y*z+5*y^2*z^2)+y^10+z^10;
  principal := ideal<P | c^2-5*C>;
  invariants := [x^2, y*z, x*(y^5+z^5), (y^5-z^5)^2, (y^5-z^5)*c];

  // The pole (sqrt5/2,0,0) represents infinity; its Borel stabilizer has order 10.
  // The weight-5 generator is fixed, since A5 has no nontrivial character.
  L<epsilon> := CyclotomicField(5);
  PE<X,Y,Z,cc> := PolynomialRing(L, [1, 1, 1, 5]);
  rot := DiagonalMatrix(L, [1, epsilon, epsilon^-1]);
  flip := Matrix(L, 3, 3, [-1,0,0, 0,0,-1, 0,-1,0]);
  G := MatrixGroup<3,L | rot, flip>;
  assert #G eq 10;
  actions := [[X,epsilon*Y,epsilon^-1*Z,cc], [-X,-Z,-Y,cc]];
  identity := [PE.i : i in [1..4]];
  assert &and[Evaluate(C,im) eq Evaluate(C,identity) : im in actions];
  assert &and[Evaluate(f,im) eq Evaluate(f,identity)
    : f in invariants, im in actions];

  // C5 invariants are x,yz,y^5,z^5. The involution fixes y^5-z^5 and
  // negates x and y^5+z^5. Taking even weights after adjoining c gives
  // u,v,w,s,t below; c^2 = 5*C eliminates the remaining product c^2.
  u := Rsrc.1; v := Rsrc.2; w := Rsrc.3; s := Rsrc.4; t := Rsrc.5;
  Pc := 320*u^3*v^2-160*u^2*v^3+20*u*v^4+8*v^5
    -4*w*(32*u^2-20*u*v+5*v^2);
  I := ideal<Rsrc | w^2-u*(s+4*v^5), t^2-5*s*(s+Pc)>;
  assert IsHomogeneous(I);
  assert &and[Evaluate(f,invariants) in principal : f in Generators(I)];

  // The Molien series verifies that these relations give the entire kernel.
  Qq<q> := RationalFunctionField(Rationals());
  cyc := (1+q^5)/((1-q)*(1-q^2)*(1-q^5));
  molien := (cyc+1/((1-q)*(1+q)^2))/2*(1+q^5);
  molien := (molien+Evaluate(molien,-q))/2;
  assert Qq!HilbertSeries(I) eq molien;

  p := Rtgt.1; q := Rtgt.2; r := Rtgt.3; h := Rtgt.4; j := Rtgt.5;
  PhiImages := [ Rtgt |
    (p+5*q)/60,
    (p-q)/12,
    100*r+(p-q)^3/1728,
    100000*j-(p-q)^5/124416,
    (-41*p^5+325*p^4*q-890*p^3*q^2+1130*p^2*q^3-685*p*q^4+161*q^5)/3110400
      +(35*p^2-670*p*q+635*q^2)*r/18+8000*h-84000*j
  ];
  PsiImages := [ Rsrc |
    10*u+10*v,
    10*u-2*v,
    (w-v^3)/100,
    -3/500*u*v^4+217/100000*v^5+1/200*u*v*w-27/20000*v^2*w
      +21/200000*s+1/8000*t,
    1/50000*v^5+1/100000*s
  ];
  citation := "the even D5 invariants of Hirzebruch, LNM 627 (1977), pp.305-310, with c^2 = 5*C";
  return I, PhiImages, PsiImages, citation;
end function;
return LitData;
