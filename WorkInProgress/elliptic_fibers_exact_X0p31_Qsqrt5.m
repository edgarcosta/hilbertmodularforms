/*
  Singular-fibre configuration of the elliptic fibration on X_0(p31)/Q(sqrt5),
  proved UNCONDITIONALLY OVER Q (height-free).  Companion to
  elliptic_fibers_X0p31_Qsqrt5.m (which does the same over F_p by sampling+CRT).

  RESULT:  the functional invariant j(t) = N(t)/D(t) in Q(t), deg N = deg D = 24,
  and D factors over Q as
        D = l6^6 * l2^2 * q4^4 * o8       (l6,l2 linear; q4 irred deg 2; o8 irred deg 8),
  giving singular fibres
        I_6 + I_2  (both rational)  +  2 I_4 (a conjugate pair)  +  8 I_1 (one Galois orbit),
  together with the double fibre _2 I_0 at t=0.  Sum e(F_v) = 24 = e(Y).

  WHY OVER Q AND NOT CRT:  j(t) is defined over Q but its coefficients have very
  large height (j(7) already has ~130-digit numerator/denominator), so CRT over a
  feasible number of primes cannot reconstruct it.  Instead we evaluate j(t0) in Q
  EXACTLY at rational t0 and interpolate; agreement of N/D with j at 72 > 49 exact
  points is a polynomial identity in Q(t), needing no height or reduction bound.

  METHOD (exact j(t0) in Q, no rational point on the fibre required):
    * adjoin F1 - t0 F2 to the model ideal (cuts X to the 1-dim fibre) and, in the
      chart Omega=x3=1, eliminate nine of the ten weight->=6 generators, keeping
      the weight-2 coords x1,x2 and one weight-6 coord x4;
    * the relation quadratic in x4 presents the fibre as a double cover
      y^2 = W(x1,x2) of the conic {F1 - t0 F2 = 0};
    * the conic has a rational point, so parametrising it over Q yields a
      hyperelliptic model y^2 = h(s), deg h = 4, and j(t0) = jInvariant of the
      Jacobian of its genus-one (binary-quartic) model.
*/

AttachSpec("spec");
SetColumns(0);
Q := Rationals();
// pencil generators (coeffs in [x1^2,x1*x2,x1,x2^2,x2,1], x3=Omega=1); see
// elliptic_fibration_X0p31_Qsqrt5.m
c1 := [-7271/133171200, 3497351/66585600, -7271/36992, -6987431/133171200, -225401/36992, -92551/9248];
c2 := [-9169/11097600, 4410289/5548800, -27507/9248, -8811409/11097600, -852717/9248, -228051/2312];
load "Verification/CanonicalRingEquations/2.2.5.1-31.2-gl-0.m";   // R, eqns

jOverQ := function(t0)   // exact j-invariant in Q of the fibre over t0, or false
  P12<X5,X6,X7,X8,X9,X10,X11,X12,X13, X1,X2,X4> := PolynomialRing(Q, 12, "elim", 9);
  h := hom< R -> P12 | [X1, X2, P12!1, X4, X5, X6, X7, X8, X9, X10, X11, X12, X13] >;
  mm := [X1^2, X1*X2, X1, X2^2, X2, P12!1];
  F1 := &+[c1[i]*mm[i]:i in [1..6]]; F2 := &+[c2[i]*mm[i]:i in [1..6]];
  J := EliminationIdeal(ideal< P12 | [h(e) : e in eqns] cat [F1 - t0*F2] >, 9);
  Q3<x1,x2,x4> := PolynomialRing(Q, 3);
  gg := [hom< P12 -> Q3 | [Q3|0,0,0,0,0,0,0,0,0, x1, x2, x4] >(g) : g in Basis(J)];
  cs := [g : g in gg | Degree(g,x4) eq 0]; if #cs eq 0 then return false, Q!0; end if;
  conic := cs[1];
  q2 := [g : g in gg | Degree(g,x4) eq 2]; if #q2 eq 0 then return false, Q!0; end if;
  cf := Coefficients(q2[1], x4);
  W := NormalForm(cf[2]^2 - 4*cf[3]*cf[1], ideal< Q3 | conic >);   // y^2 = W on the conic
  if W eq 0 then return false, Q!0; end if;
  R2<a,b> := PolynomialRing(Q,2);
  Ph<A,B,C> := ProjectiveSpace(Q,2);
  Cc := Conic(Ph, Homogenization(Evaluate(hom<Q3->R2|[a,b,R2!0]>(conic),[A,B]), C));
  if not HasRationalPoint(Cc) then return false, Q!0; end if;
  par := Parametrization(Cc); feq := DefiningEquations(par);
  S1 := CoordinateRing(Ambient(Domain(par)));
  PH<AA,BB,CC> := PolynomialRing(Q,3);
  Wh := Homogenization(hom< Q3 -> PH | [AA, BB, PH!0] >(W), CC, 16);   // deg 16 in (AA,BB,CC)
  numsu := hom< PH -> S1 | [S1!feq[1], S1!feq[2], S1!feq[3]] >(Wh);
  St<ss> := PolynomialRing(Q);
  num := hom< S1 -> St | [ss, St!1] >(numsu);
  if num eq 0 then return false, Q!0; end if;
  hpoly := &*[St| f[1]^(f[2] mod 2) : f in Factorization(num)];   // squarefree odd part
  if not (Degree(hpoly) in [3,4]) then return false, Q!0; end if;
  return true, jInvariant(Jacobian(GenusOneModel(hpoly)));
end function;

// exact j(t0) at t0 = 1..NT (smooth fibres)
NT := 72;
pts := [];
for t0 in [1..NT] do
  ok, jj := jOverQ(Q!t0);
  if ok then Append(~pts, <t0, jj>); end if;
end for;
printf "exact j(t0) computed at %o smooth fibres\n", #pts;
assert #pts ge 51;

// interpolate N/D (D monic, deg 24) from the first 49 points: solve A*x = b over Q
Qt<t> := PolynomialRing(Q);
rows := []; rhs := [];
for i in [1..49] do
  ti := Q!pts[i][1]; ji := pts[i][2];
  Append(~rows, [ti^k : k in [0..24]] cat [-ji*ti^k : k in [0..23]]);
  Append(~rhs, ji*ti^24);
end for;
x := Solution(Transpose(Matrix(Q, rows)), Vector(Q, rhs));   // A*x = b
N := Qt![x[k] : k in [1..25]];
D := Qt!([x[k] : k in [26..49]] cat [Q!1]);

// height-free certificate: exact identity at ALL sampled points (72 > 24+24+1)
val := function(P) return &and[Evaluate(D,Q!q[1]) ne 0 and
        Evaluate(N,Q!q[1])/Evaluate(D,Q!q[1]) eq q[2] : q in P]; end function;
assert val(pts);
printf "N/D = j proved: exact identity holds at all %o points (> 49), so N/D = j in Q(t).\n", #pts;

FD := Factorization(D);
part := Reverse(Sort(&cat[[f[2] : i in [1..Degree(f[1])]] : f in FD]));
printf "\nD(t) over Q  (exponent = I_n index):\n";
for f in FD do printf "  (deg %o irred)^%o -> %o fibre(s) I_%o\n", Degree(f[1]), f[2], Degree(f[1]), f[2]; end for;
printf "  PARTITION = %o  (sum = %o = e(Y))\n", part, &+part;
printf "N [j=0]      : %o\n", [<Degree(f[1]),f[2]> : f in Factorization(N)];
printf "N-1728 D [j=1728]: %o\n", [<Degree(f[1]),f[2]> : f in Factorization(N-1728*D)];
printf "j(0) is finite (double fibre _2 I_0): %o\n", Evaluate(D,Q!0) ne 0;
exit;
