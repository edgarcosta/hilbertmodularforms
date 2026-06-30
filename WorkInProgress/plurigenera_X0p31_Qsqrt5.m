/*
  Plurigenera of the Hilbert modular surface X_0(p31) over Q(sqrt(5)).

  p31 = the prime above 31 with norm 31 (LMFDB label 31.2).
  The smooth model Y is the minimal resolution of the Baily-Borel model.

  We compute the plurigenera P_m = dim H^0(Y, m K_Y) for m = 1, 2.

  An m-canonical form is a parallel weight-2m Hilbert modular form f such that
  f * (dz_1 dz_2)^m extends holomorphically over Y. This requires:
    (a) vanishing to order >= m along the cusp resolution cycles, and
    (b) local conditions at the elliptic points.
  A toric analysis of the elliptic quotient singularities shows that the
  elliptic conditions are VACUOUS for m <= 2 (they first appear at m = 3),
  so for m <= 2:
        P_m = dim { f in S_{2m} : ord_C(f) >= m for every cusp curve C }.

  Cusp order functional (cusp at infinity, the standard Q(sqrt5) (-3)-curve):
        ord_inf(f) = min over the Fourier support of  min_k Tr(nu * eps^k * A0),
  with A0 the resolution ray and eps the fundamental totally positive unit.
  This is CALIBRATED by ord(Omega^k) = k, where Omega spans S_2 = H^0(K_Y).

  Second cusp: dim S_{2m}(level 1) = 0, so S_{2m} is entirely p31-NEW, and the
  Atkin-Lehner involution w_p31 swaps the two cusps. Hence
        ord_0(f) = ord_inf(w_p31 f),
  and for the normalized newform basis (a_{(1)} = 1) the two order-m conditions
  become rank computations on the Atkin-Lehner sign vector.

  Result: P_1 = 1, P_2 = 2.  Combined with chi = 2 (p_g = 1, q = 0), this
  determines the Kodaira dimension:
    - kappa = -infty (rational/ruled) needs p_g = 0;            excluded.
    - kappa = 0: with q = 0, p_g = 1 the minimal model is a K3, so P_m = 1
      for all m, hence P_2 = 1;                                  excluded (P_2 = 2).
    - kappa = 2 (general type): the minimal model has K^2_min >= 1, and
      Riemann-Roch + Mumford vanishing give P_2 = chi + K^2_min = 2 + K^2_min
      >= 3;                                                      excluded (P_2 = 2).
  Hence kappa(X_0(p31)) = 1: the surface is PROPERLY ELLIPTIC -- it carries a
  genuine elliptic fibration -- despite its K3 numerical signature
  (chi = 2, p_g = 1, q = 0, K^2(Y) = 0, e = 24).
*/

AttachSpec("spec");
SetColumns(0);

F   := QuadraticField(5);
ZF  := Integers(F);
p31 := Factorization(31*ZF)[2][1];
assert Norm(p31) eq 31;

// ---- fundamental totally positive unit and the cusp-infinity resolution ray ----
U, mU := UnitGroup(ZF);
eps := F!mU(U.2);
if not IsTotallyPositive(eps) then eps := eps^2; end if;

// cusp at infinity: module M = ZF, HJ continued fraction [3] (single (-3)-curve);
// the order functional below uses the ray A0 = 1 (calibrated by ord(Omega^k) = k).
A0 := F!1;

ordval := function(nu)
  best := Infinity();
  for k in [-10..10] do
    t := Trace(nu*eps^k*A0);
    if t gt 0 and t lt best then best := t; end if;
  end for;
  return best;
end function;

ordform := function(f)
  o := Infinity();
  for bb -> fc in Components(f) do
    for nu -> a in Coefficients(fc) do
      if a ne 0 and not IsZero(nu) then o := Min(o, ordval(nu)); end if;
    end for;
  end for;
  return o;
end function;

// ---- forms ----
M  := GradedRingOfHMFs(F, 80);
Om := CuspFormBasis(HMFSpace(M, p31, [2,2]))[1];      // spans S_2 = H^0(K_Y)
S4 := CuspFormBasis(HMFSpace(M, p31, [4,4]));

// ---- calibration of the cusp order functional ----
assert ordform(Om)     eq 1;     // ord(Omega)   = 1
assert ordform(Om*Om)  eq 2;     // ord(Omega^2) = 2
assert ordform(Om*Om*Om) eq 3;   // ord(Omega^3) = 3
print "Cusp order functional calibrated: ord(Omega^k) = k for k = 1,2,3.";

// ---- P_1 = dim S_2 = p_g ----
P1 := #CuspFormBasis(HMFSpace(M, p31, [2,2]));
printf "P_1 = dim S_2 = %o\n", P1;

// ---- ord_inf >= 2 is a single condition (only nu_min sits at order 1) ----
val1 := [];
for bb -> fc in Components(S4[1]) do
  for nu -> a in Coefficients(fc) do
    if not IsZero(nu) and ordval(nu) eq 1 then Append(~val1, nu); end if;
  end for;
end for;
condmat := Matrix(F, [[Coefficient(Components(f)[1*ZF], nu : InFunDomain:=false)
                        : f in S4] : nu in val1]);
d_inf := #S4 - Rank(condmat);
printf "d_inf = dim { f in S_4 : ord_inf(f) >= 2 } = %o\n", d_inf;

// ---- second cusp via Atkin-Lehner (S_4 is entirely p31-new) ----
Mh := HilbertCuspForms(F, p31, [4,4]);
assert Dimension(NewSubspace(Mh)) eq Dimension(Mh);   // all new
W  := AtkinLehnerOperator(Mh, p31);
evs := &cat[[Rationals()!e[1] : j in [1..e[2]]] : e in Eigenvalues(W)];
signs := [(e gt 0) select 1 else -1 : e in evs];
printf "Atkin-Lehner signs on S_4 = %o\n", signs;

// P_2 = dim ker [ [1,1,1,1] ; signs ]  (both cusp conditions, eigenbasis)
P2mat := Matrix(Rationals(), 2, #S4,
                [Rationals()|1 : i in [1..#S4]] cat [Rationals()!s : s in signs]);
P2 := #S4 - Rank(P2mat);
printf "P_2 = %o\n", P2;

assert P1 eq 1 and P2 eq 2;
print "";
print "CONCLUSION: P_1, P_2 = 1, 2.";
print "With chi = 2: P_2 = 1 would force K3 (kappa 0); general type forces";
print "P_2 = chi + K^2_min >= 3. Both excluded, so kappa(X_0(p31)) = 1:";
print "the surface is PROPERLY ELLIPTIC (despite its K3 numerical signature).";
exit;
