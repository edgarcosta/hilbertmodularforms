// Worked example (SLOW, CI-skipped): the singular-fibre configuration of the
// elliptic fibration on X_0(p31) over Q(sqrt 5), proved UNCONDITIONALLY over Q.
//
// Run manually:
//   magma -b filename:=examples/slow/X0p31_elliptic_fibres.m exitsignal:='' run_tests.m
// (~1 hour: 72 exact fibre solves over Q.)
//
// The Iitaka fibration f : Y -> P^1 is the bicanonical conic pencil (see
// examples/X0p31_plurigenera.m).  Its functional invariant j(t) = N(t)/D(t) in
// Q(t) has deg N = deg D = 24, and D factors over Q as
//     D = l6^6 * l2^2 * q4^4 * o8      (l6,l2 linear; q4 irred deg 2; o8 irred deg 8),
// giving singular fibres
//     I_6 + I_2 (both rational) + 2 I_4 (a conjugate pair) + 8 I_1 (one Galois orbit),
// plus the double fibre _2 I_0 at t = 0.  Sum e(F_v) = 24 = e(Y).
//
// Method (exact j(t0) in Q, no rational point on the fibre needed): adjoin the
// pencil equation F1 - t0 F2 to the saved Baily-Borel model to cut out the
// fibre; eliminate the nine weight->=6 generators (chart Omega=x3=1), keeping
// x1,x2,x4; the relation quadratic in x4 presents the fibre as a double cover
// y^2 = W of the conic {F1 - t0 F2 = 0}; parametrise the conic over Q (it has a
// rational point) to get a hyperelliptic model y^2 = h(s), deg h = 4, and read
// j(t0) off the Jacobian of its genus-one model.  Then N/D is recovered by exact
// rational interpolation and PROVED equal to j by the exact identity holding at
// 72 > 49 = deg N + deg D + 1 points -- a polynomial identity in Q(t), with no
// height or reduction hypothesis.  Cf. examples/X0p31_plurigenera.m (fast, exact
// P_1,P_2 and the m=2 certificate) and the mod-p version in WorkInProgress/.
//
// Written flat (no procedure wrapper): the runner evaluates this file in `eval`.

Q := Rationals();
// pencil generators F1, F2 (coeffs in [x1^2,x1*x2,x1,x2^2,x2,1], x3=Omega=1)
c1 := [-7271/133171200, 3497351/66585600, -7271/36992, -6987431/133171200, -225401/36992, -92551/9248];
c2 := [-9169/11097600, 4410289/5548800, -27507/9248, -8811409/11097600, -852717/9248, -228051/2312];
J0 := LoadStoredCanonicalRing("2.2.5.1-31.2");    // the saved Baily-Borel model
R := Generic(J0);  eqns := Basis(J0);

jOverQ := function(t0)   // exact j-invariant in Q of the fibre over t0, or false
  P12<X5,X6,X7,X8,X9,X10,X11,X12,X13, X1,X2,X4> := PolynomialRing(Q, 12, "elim", 9);
  h := hom< R -> P12 | [X1, X2, P12!1, X4, X5, X6, X7, X8, X9, X10, X11, X12, X13] >;
  mm := [X1^2, X1*X2, X1, X2^2, X2, P12!1];
  F1 := &+[c1[i]*mm[i]:i in [1..6]]; F2 := &+[c2[i]*mm[i]:i in [1..6]];
  J := EliminationIdeal(ideal< P12 | [h(e) : e in eqns] cat [F1 - t0*F2] >, 9);
  Q3<x1,x2,x4> := PolynomialRing(Q, 3);
  gg := [hom< P12 -> Q3 | [Q3|0,0,0,0,0,0,0,0,0, x1, x2, x4] >(g) : g in Basis(J)];
  cs := [g : g in gg | Degree(g,x4) eq 0]; if #cs eq 0 then return false, Q!0; end if;
  q2 := [g : g in gg | Degree(g,x4) eq 2]; if #q2 eq 0 then return false, Q!0; end if;
  cf := Coefficients(q2[1], x4);
  W := NormalForm(cf[2]^2 - 4*cf[3]*cf[1], ideal< Q3 | cs[1] >);   // y^2 = W on the conic
  if W eq 0 then return false, Q!0; end if;
  R2<a,b> := PolynomialRing(Q,2);
  Ph<A,B,C> := ProjectiveSpace(Q,2);
  Cc := Conic(Ph, Homogenization(Evaluate(hom<Q3->R2|[a,b,R2!0]>(cs[1]),[A,B]), C));
  if not HasRationalPoint(Cc) then return false, Q!0; end if;
  par := Parametrization(Cc); feq := DefiningEquations(par);
  S1 := CoordinateRing(Ambient(Domain(par)));
  PH<AA,BB,CC> := PolynomialRing(Q,3);
  Wh := Homogenization(hom< Q3 -> PH | [AA, BB, PH!0] >(W), CC, 16);
  num := hom< S1 -> PolynomialRing(Q) | [PolynomialRing(Q).1, 1] >(
           hom< PH -> S1 | [S1!feq[1], S1!feq[2], S1!feq[3]] >(Wh));
  if num eq 0 then return false, Q!0; end if;
  hpoly := &*[PolynomialRing(Q)| f[1]^(f[2] mod 2) : f in Factorization(num)];  // sqfree odd part
  if not (Degree(hpoly) in [3,4]) then return false, Q!0; end if;
  return true, jInvariant(Jacobian(GenusOneModel(hpoly)));
end function;

// exact j(t0) at t0 = 1..72 (smooth fibres)
pts := [];
for t0 in [1..72] do
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
assert Degree(N) eq 24 and Degree(D) eq 24 and IsMonic(D);

// height-free certificate: exact identity at ALL sampled points (72 > 24+24+1)
assert &and[ Evaluate(D,Q!q[1]) ne 0 and
             Evaluate(N,Q!q[1])/Evaluate(D,Q!q[1]) eq q[2] : q in pts ];
printf "N/D = j proved: exact identity holds at all %o points (> 49), so N/D = j in Q(t).\n", #pts;

// factor D over Q: pole orders are the I_n indices
FD   := Factorization(D);
part := Reverse(Sort(&cat[[f[2] : i in [1..Degree(f[1])]] : f in FD]));
assert part eq [6,4,4,2,1,1,1,1,1,1,1,1];        // I_6 + 2 I_4 + I_2 + 8 I_1
assert &+part eq 24;                             // = e(Y)
assert {* Degree(f[1]) : f in FD | f[2] eq 4 *} eq {* 2 *};   // the two I_4 are a conjugate pair
assert Evaluate(D,Q!0) ne 0;                     // t=0 not a pole: double fibre _2 I_0
// forced ramification of a genuine functional invariant
assert {* f[2] : f in Factorization(N) *}        eq {* 3^^#Factorization(N) *};   // j=0 : all mult 3
assert {* f[2] : f in Factorization(N-1728*D) *} eq {* 2^^#Factorization(N-1728*D) *}; // j=1728: mult 2

printf "singular fibres: I_6 + 2 I_4 + I_2 + 8 I_1  (sum e = 24 = e(Y)),  + double fibre _2 I_0.\n";
