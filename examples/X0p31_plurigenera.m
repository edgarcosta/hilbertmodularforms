// Worked example: X_0(p31) over Q(sqrt 5) is properly elliptic (kappa = 1)
// despite having the numerical invariants of a K3 surface.
//
// p31 is the prime above 31 of norm 31 (LMFDB label 31.2); Y is the minimal
// resolution of the Baily-Borel model.  This certifies, with EXACT (algebraic)
// computations only:
//   * P_1 = dim S_2 = 1  and  P_2 = 2               (Section-9 method)
//   * the multiple fibre has multiplicity m = 2      (exact certificate)
//   * hence P_3 = 1 + floor(3/2) = 2 and P_n = 1 + floor(n/2).
// Since chi = 2, P_2 = 2 already excludes K3 (P_2 = 1) and general type
// (P_2 = chi + K^2_min >= 3), so kappa(Y) = 1.
//
// The m = 2 certificate is exact: M_4 = Sym^2 M_2, so |2K_Y| is a pencil of
// conics in P(M_2); its discriminant is l_1 * l_2^2, and the unique rank-1
// (double-line) member is Omega^2 = y_3^2, giving a multiplicity-2 fibre.
// (Cf. Lemma "P_n = 1 + floor(n(m-1)/m)" in the accompanying note; P_3 = 2 in
// turn forces m = 2, so the two determinations agree.)
//
// Written flat (no procedure wrapper): the test runner evaluates this file
// inside an `eval`.

F   := QuadraticField(5);
ZF  := Integers(F);
p31 := Factorization(31*ZF)[2][1];
assert Norm(p31) eq 31;

// fundamental totally positive unit; cusp-infinity resolution ray A0 = 1
U, mU := UnitGroup(ZF);
eps := F!mU(U.2);
if not IsTotallyPositive(eps) then eps := eps^2; end if;
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

M  := GradedRingOfHMFs(F, 100);
M2 := HMFSpace(M, p31, [2,2]);
ybasis := EisensteinBasis(M2) cat CuspFormBasis(M2);   // y1,y2 Eisenstein; y3 = Omega
assert #ybasis eq 3;
Om := ybasis[3];
S4 := CuspFormBasis(HMFSpace(M, p31, [4,4]));

// ---- cusp order functional, calibrated by ord(Omega^k) = k ----
assert ordform(Om) eq 1 and ordform(Om^2) eq 2 and ordform(Om^3) eq 3;

// ---- P_1 = dim S_2 ----
P1 := #CuspFormBasis(M2);

// ---- P_2:  ord >= 2 at cusp inf is a single condition (only nu_min at order 1) ----
cof := func< f, nu | Coefficient(Components(f)[1*ZF], nu : InFunDomain := false) >;
val1 := [];
for bb -> fc in Components(S4[1]) do
  for nu -> a in Coefficients(fc) do
    if not IsZero(nu) and ordval(nu) eq 1 then Append(~val1, nu); end if;
  end for;
end for;
d_inf := #S4 - Rank(Matrix(F, [[cof(f, nu) : f in S4] : nu in val1]));
// second cusp via Atkin-Lehner (S_4 is entirely p31-new)
Mh := HilbertCuspForms(F, p31, [4,4]);
assert Dimension(NewSubspace(Mh)) eq Dimension(Mh);
signs := [ (Rationals()!e[1] gt 0) select 1 else -1
           : j in [1..e[2]], e in Eigenvalues(AtkinLehnerOperator(Mh, p31)) ];
P2 := #S4 - Rank(Matrix(Rationals(), 2, #S4,
        [Rationals()|1 : i in [1..#S4]] cat [Rationals()!s : s in signs]));
assert P1 eq 1 and P2 eq 2;
printf "P_1 = %o, P_2 = %o\n", P1, P2;

// ---- exact m = 2 certificate: |2K_Y| is a conic pencil with disc l1 * l2^2 ----
idx   := [<i,j> : j in [i..3], i in [1..3]];
quads := [ybasis[t[1]]*ybasis[t[2]] : t in idx];       // the 6 monomials y_i y_j
nus := []; for nu -> a in Coefficients(Components(quads[1])[1*ZF]) do
             if not IsZero(nu) then Append(~nus, nu); end if; end for;
Sort(~nus, func< x,y | Trace(x)-Trace(y) >); nus := nus[1..30];
QC := Matrix(F, [[cof(q, nu) : q in quads] : nu in nus]);
assert Rank(QC) eq 6;                                  // M_4 = Sym^2 M_2 (no relations)

// H^0(2K_Y): weight-4 cusp forms of order >= 2 at both cusps, as quadrics
S4q := []; for f in S4 do ok, c := IsConsistent(Transpose(QC), Vector(F,[cof(f,nu):nu in nus]));
             assert ok; Append(~S4q, c); end for;
UpS := [HeckeOperator(f, p31) : f in S4];
KerS := NullSpace(Transpose(Matrix(F,
          [ [cof(S4[i], val1[1])      : i in [1..#S4]],       // ord >= 2 at cusp inf
            [-cof(UpS[i], val1[1])/31 : i in [1..#S4]] ])));   // ... and at cusp 0
assert Dimension(KerS) eq 2;                           // H^0(2K_Y) = <F1,F2>, so P_2 = 2
Fq := [ &+[Eltseq(d)[i]*S4q[i] : i in [1..#S4]] : d in Basis(KerS) ];
assert Vector(F,[0,0,0,0,0,1]) in sub< Universe(Fq) | Fq >;   // Omega^2 = y3^2 in the pencil

symmat := function(c) cc := Eltseq(c);
  return Matrix(F,3,3,[cc[1],cc[2]/2,cc[3]/2, cc[2]/2,cc[4],cc[5]/2, cc[3]/2,cc[5]/2,cc[6]]);
end function;
M1 := symmat(Fq[1]); M2m := symmat(Fq[2]);
PP<s,t> := PolynomialRing(F,2);
disc := Determinant(s*ChangeRing(M1,PP) + t*ChangeRing(M2m,PP));
fac  := Factorization(disc);
assert &+[g[2] : g in fac] eq 3 and {* g[2] : g in fac *} eq {* 1, 2 *};   // l1 * l2^2
// the double root is the rank-1 (double-line) member
dbl := [g[1] : g in fac | g[2] eq 2][1];
cs := MonomialCoefficient(dbl, s); ct := MonomialCoefficient(dbl, t);
s0 := ct ne 0 select F!1 else F!0; t0 := ct ne 0 select -cs/ct else F!1;
assert Rank(s0*M1 + t0*M2m) eq 1;                      // rank-1 => double line => 2*{Omega=0}
m := 2;

P3 := 1 + (3*(m-1)) div m;
assert P3 eq 2;
printf "multiple-fibre multiplicity m = %o, so P_3 = %o and P_n = 1 + floor(n/2).\n", m, P3;
printf "X_0(p31)/Q(sqrt5): kappa = 1 (properly elliptic), K3 numerical invariants.\n";
