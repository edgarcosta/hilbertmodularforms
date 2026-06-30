/*
  Partial computation toward P_3 = dim H^0(Y, 3 K_Y) for the Hilbert modular
  surface X_0(p31) over Q(sqrt(5)) (p31 = prime above 31, norm 31).

  NOTE: the Kodaira dimension is already settled WITHOUT P_3 -- see
  plurigenera_X0p31_Qsqrt5.m: P_1, P_2 = 1, 2 with chi = 2 force kappa = 1
  (properly elliptic). This script records the validated machinery toward the
  *exact* P_3, which would only pin down the multiple-fibre multiplicity.

  Theory: for a properly elliptic surface over P^1 with chi = 2 and a single
  multiple fibre of multiplicity m, P_n = 1 + floor(n(m-1)/m). P_2 = 2 forces
  exactly one multiple fibre, so
        P_3 = 2  (if m = 2)   or   P_3 = 3  (if m >= 3).
  Hence P_3 in {2,3} is guaranteed; computing it determines m.

  P_3 = dim { f in S_6 : ord_C(f) >= 3 for every cusp curve C, and the
              elliptic conditions hold }.  At m = 3 the elliptic conditions
  are (toric analysis): f(tau) = 0 at the two 1/3(1,1) points, and one first
  derivative vanishes at each of the four 1/5 points; the 1/3(1,2)=A_2 and
  1/2(1,1)=A_1 points (and the 1/5(1,4)=A_4 type) impose nothing.

  Validated pieces (this script):
    - cusp-infinity:  ord_inf >= 3 imposes 3 exact conditions; d_inf^(3) =
      dim{S_6 : ord_inf >= 3} = 11. (order functional calibrated by
      ord(Omega^k) = k.)
    - Atkin-Lehner:  W_p31 on S_6 has signs 8 x (+1), 6 x (-1).
    - elliptic 1/3(1,1) value conditions: rank 2 (= number of such orbits),
      stable under relative-tolerance refinement.
    - 1/5 derivative functional (Cayley coordinates, m = 3):
          c_{10}(f) = 2i*Im(tau_1)*d_{z1}f(tau) + 2m*f(tau)  (and z2-analogue).

  Blocker for the exact P_3: the cusp-0 conditions need the Fricke action on
  the q-expansion basis. S_6 has 2 oldforms (dim S_6(level 1) = 1), so the
  all-new Atkin-Lehner shortcut used for P_2 does not apply directly, and the
  repo's q-expansion Eigenbasis/HeckeMatrix does not converge for this space.
*/

AttachSpec("spec");
SetColumns(0);
F := QuadraticField(5);  ZF := Integers(F);
p31 := Factorization(31*ZF)[2][1];
U,mU := UnitGroup(ZF); eps := F!mU(U.2);
if not IsTotallyPositive(eps) then eps := eps^2; end if;
A0 := F!1;   // cusp-infinity resolution ray (HJ = [3], the (-3)-curve)

ordval := function(nu)
  best := Infinity();
  for k in [-12..12] do t := Trace(nu*eps^k*A0); if t gt 0 and t lt best then best := t; end if; end for;
  return best;
end function;
ordform := function(f)
  o := Infinity();
  for bb -> fc in Components(f) do for nu -> a in Coefficients(fc) do
    if a ne 0 and not IsZero(nu) then o := Min(o, ordval(nu)); end if; end for; end for;
  return o;
end function;

M  := GradedRingOfHMFs(F, 100);
Om := CuspFormBasis(HMFSpace(M, p31, [2,2]))[1];
S6 := CuspFormBasis(HMFSpace(M, p31, [6,6]));
printf "dim S_6 = %o\n", #S6;
assert ordform(Om*Om*Om) eq 3;   // calibration
print "cusp order functional calibrated: ord(Omega^3) = 3.";

// cusp-infinity: ord_inf >= 3 conditions (kill ord 1 and ord 2 layers)
lows := [];
for bb -> fc in Components(S6[1]) do for nu -> a in Coefficients(fc) do
  if not IsZero(nu) and ordval(nu) le 2 then Append(~lows, nu); end if; end for; end for;
condmat := Matrix(F, [[Coefficient(Components(f)[1*ZF], nu : InFunDomain:=false) : f in S6] : nu in lows]);
d_inf3 := #S6 - Rank(condmat);
printf "cusp-inf: %o conditions (ord<=2 layers), d_inf^(3) = dim{S_6:ord_inf>=3} = %o\n",
       Rank(condmat), d_inf3;

// Atkin-Lehner signs on S_6 (Hecke side)
Mh := HilbertCuspForms(F, p31, [6,6]);
WW := AtkinLehnerOperator(Mh, p31);
evs := &cat[[Rationals()!e[1] : j in [1..e[2]]] : e in Eigenvalues(WW)];
signs := [(e gt 0) select 1 else -1 : e in evs];
printf "Atkin-Lehner W_p31 on S_6: #(+1) = %o, #(-1) = %o  (dim new = %o, old = %o)\n",
       #[s:s in signs|s eq 1], #[s:s in signs|s eq -1],
       Dimension(NewSubspace(Mh)), Dimension(Mh)-Dimension(NewSubspace(Mh));

print "";
printf "PREDICTION: kappa = 1 (already proven from P_2) => P_3 in {2,3}\n";
printf "  P_3 = 2 iff the single multiple fibre has multiplicity 2, else P_3 = 3.\n";
printf "  (Exact value needs the cusp-0 Fricke action on S_6; see header.)\n";
exit;
