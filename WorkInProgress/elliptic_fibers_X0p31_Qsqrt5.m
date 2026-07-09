/*
  Singular-fibre configuration of the elliptic fibration on the Hilbert modular
  surface X_0(p31) over Q(sqrt(5))  (p31 = prime above 31, norm 31).

  Companion to elliptic_fibration_X0p31_Qsqrt5.m, which exhibits the fibration as
  the bicanonical pencil of conics  phi = [F1:F2] : Y --> P^1  and locates the
  multiple fibre  2*{Omega=0}  at t=0.  This script determines the FULL Kodaira
  configuration of the (relatively minimal) elliptic surface.

  RESULT (confirmed mod p = 1009 and p = 2003, cross-validated on held-out and
  fresh samples):

        I_6  +  I_4  +  I_4  +  I_2  +  8 I_1     (twelve singular fibres)
        + one double fibre  _2 I_0  at t = 0  ({Omega = 0}).

     Sum e(F_v) = 6+4+4+2+8 = 24 = e(Y),   deg Delta = 24 = 12*chi,   j-map deg 24.
  Since e(Y)=24 is exhausted by the multiplicative fibres, NO additive fibre can
  occur (an I_n* would add >=6).  This is the Iitaka fibration of the properly-
  elliptic (kappa=1) surface.

  METHOD.  The full-surface / generic-t Groebner elimination blows up, but each
  INDIVIDUAL fibre is cheap:  adjoining the pencil equation F1 - t0*F2 first makes
  the fibre a curve (1-dim), so eliminating the 9 higher-weight generators (keeping
  the weight-2 coords x1,x2 and one weight-6 coord x4) runs in ~16s over GF(p).
  A second elimination of x1 gives a plane model G(x2,x4) BIRATIONAL to the fibre
  (a generator is linear in x1, so the projection is 1:1 -- not the hyperelliptic
  quotient), of genus 1.  Magma's GenusOneModel fails on it, but one point (sample
  x2, factor the quartic in x4) + EllipticCurve(.,pt) gives the Weierstrass model
  and hence j(t0).  Sampling j over many t0 and rational-reconstructing j(t)=N/D
  (degN=degD=24) yields the pole partition of D = the I_n indices.

  NB: 48 samples give a SPURIOUS (23,24) overfit; the true (24,24) map needs >=50
  points.  We fit on 50 and cross-check on the rest.

  F1, F2 below are the pencil generators from elliptic_fibration_X0p31_Qsqrt5.m,
  written in the monomial basis [y1^2, y1*y2, y1*y3, y2^2, y2*y3, y3^2] of Sym^2 M_2
  with the weight-2 coords dehomogenized at y3 = Omega = 1  (so the conic is in
  y1=x1, y2=x2).
*/

AttachSpec("spec");
SetColumns(0);

// pencil generators F1, F2 (coeffs in [x1^2, x1*x2, x1, x2^2, x2, 1], x3=y3=1)
c1 := [-7271/133171200, 3497351/66585600, -7271/36992, -6987431/133171200, -225401/36992, -92551/9248];
c2 := [-9169/11097600, 4410289/5548800, -27507/9248, -8811409/11097600, -852717/9248, -228051/2312];

load "Verification/CanonicalRingEquations/2.2.5.1-31.2-gl-0.m";   // defines R, eqns

// j-invariant of the fibre over t0, computed over the finite field k
jOfFibre := function(R, eqns, c1, c2, k, t0)
  Rp := ChangeRing(R, k);  eqnsp := [Rp!e : e in eqns];
  P12<X5,X6,X7,X8,X9,X10,X11,X12,X13, X1,X2,X4> := PolynomialRing(k, 12, "elim", 9);
  h := hom< Rp -> P12 | [X1, X2, P12!1, X4, X5, X6, X7, X8, X9, X10, X11, X12, X13] >;
  mm := [X1^2, X1*X2, X1, X2^2, X2, P12!1];
  F1 := &+[(k!c1[i])*mm[i]:i in [1..6]];  F2 := &+[(k!c2[i])*mm[i]:i in [1..6]];
  // fibre = curve; eliminate the 9 higher-weight generators keeping (x1,x2,x4)
  J := EliminationIdeal(ideal< P12 | [h(e) : e in eqnsp] cat [F1 - t0*F2] >, 9);
  E3<x1,x2,x4> := PolynomialRing(k, 3, "elim", 1);
  h3 := hom< P12 -> E3 | [E3|0,0,0,0,0,0,0,0,0, x1, x2, x4] >;
  Jx1 := EliminationIdeal(ideal< E3 | [h3(g) : g in Basis(J)] >, 1);  // eliminate x1
  A2<X,Y> := PolynomialRing(k,2);
  hp := hom< E3 -> A2 | [A2|0, X, Y] >;
  gg := [hp(g) : g in Basis(Jx1) | hp(g) ne 0];  if #gg eq 0 then return "deg"; end if;
  G := gg[1];
  U<yy> := PolynomialRing(k);  pt := 0;
  for x20 in [k!i : i in [0..600]] do
    q := Evaluate(G,[x20,yy]);  if q eq 0 then continue; end if;
    r := Roots(q);  if #r gt 0 then pt := [x20, r[1][1]]; break; end if;
  end for;
  if pt cmpeq 0 then return "nopt"; end if;
  P2<XX,YY,ZZ> := ProjectiveSpace(k,2);
  Cp := Curve(P2, Homogenization(Evaluate(G,[XX,YY]), ZZ));
  Ppt := Cp![pt[1],pt[2],1];  if IsSingular(Ppt) then return "sing"; end if;
  return jInvariant(EllipticCurve(Cp, Ppt));
end function;

// sample, reconstruct j(t)=N/D, and read the pole partition, over prime p
analyse := procedure(R, eqns, c1, c2, p, nsamp)
  k := GF(p);
  pts := [];
  for i in [1..nsamp] do
    js := jOfFibre(R, eqns, c1, c2, k, k!i);
    if Type(js) ne MonStgElt then Append(~pts, <i, js>); end if;
  end for;
  Kt<t> := PolynomialRing(k);
  xs := [k!d[1]:d in pts];  ys := [k!d[2]:d in pts];
  // Euclidean rational reconstruction, stopping at deg < 25 (target (24,24))
  L := Interpolation(xs[1..50], ys[1..50]);  M := &*[t-x : x in xs[1..50]];
  r0:=M; r1:=L; s0:=Kt!0; s1:=Kt!1;
  while Degree(r1) ge 25 do q := r0 div r1; r0,r1:=r1,r0-q*r1; s0,s1:=s1,s0-q*s1; end while;
  N := r1/LeadingCoefficient(s1);  D := s1/LeadingCoefficient(s1);
  bad := [x : x in pts | Evaluate(D,k!x[1]) eq 0 or Evaluate(N,k!x[1])/Evaluate(D,k!x[1]) ne k!x[2]];
  printf "p=%o: %o smooth samples, fit on 50 -> degN=%o degD=%o, mismatches over all = %o\n",
         p, #pts, Degree(N), Degree(D), #bad;
  printf "  pole partition of j (= I_n indices):";
  part := Reverse(Sort(&cat[[f[2] : i in [1..Degree(f[1])]] : f in Factorization(D)]));
  printf " %o   (sum = e(Y) = %o)\n", part, &+part;
  printf "  j(0) = %o (double fibre _2 I_0, finite j)\n", Evaluate(N,k!0)/Evaluate(D,k!0);
end procedure;

analyse(R, eqns, c1, c2, 1009, 66);
analyse(R, eqns, c1, c2, 2003, 64);
exit;
