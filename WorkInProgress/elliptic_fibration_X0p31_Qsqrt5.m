/*
  The elliptic fibration on the Hilbert modular surface X_0(p31) over Q(sqrt(5))
  (p31 = the prime above 31, norm 31).

  This surface is properly elliptic (kappa = 1) with plurigenera P_n = 1+floor(n/2)
  -- see plurigenera_X0p31_Qsqrt5.m and plurigenera_P3_X0p31_Qsqrt5.m.  Its
  Iitaka/elliptic fibration is the bicanonical pencil |2K_Y| = <F1,F2>:
        phi = [F1:F2] : Y --> P^1.

  Clean structure.  The canonical ring is generated in weights 2,6,10 and
  dim M_4 = 6 = dim Sym^2 M_2, so  M_4 = Sym^2 M_2.  Hence the two pluricanonical
  forms are QUADRICS in the three weight-2 forms, and the fibration factors as
        Y --[y1:y2:y3]--> P^2 = P(M_2)  -->  P^1  (a pencil of conics),
  where y1,y2 are Eisenstein and y3 = Omega is the weight-2 cusp form.

  What this script shows:
    (1) H^0(2K_Y) = <F1,F2> is 2-dimensional (two explicit conics in y1,y2,y3),
        and Omega^2 = y3^2 lies in the pencil.
    (2) The discriminant det(s*M1 + t*M2) of the conic pencil factors as
        (linear)^1 * (linear)^2; the simple root is a rank-2 member (nodal
        fibre = two lines), the DOUBLE root is the rank-1 member = Omega^2 = y3^2,
        a DOUBLE LINE.
    (3) Therefore the multiplicity-2 multiple fibre is  2 * {Omega = 0}:
        the multiple fibre sits exactly at the zero locus of the weight-2 cusp
        form.  (This is the geometric realization of P_3 = 2.)
*/

AttachSpec("spec");
SetColumns(0);
F := QuadraticField(5);  ZF := Integers(F);
p31 := Factorization(31*ZF)[2][1];
U,mU := UnitGroup(ZF); epsu := F!mU(U.2);
if not IsTotallyPositive(epsu) then epsu := epsu^2; end if;
ordval := function(nu) b:=Infinity(); for k in [-12..12] do t:=Trace(nu*epsu^k); if t gt 0 and t lt b then b:=t; end if; end for; return b; end function;

Mgr := GradedRingOfHMFs(F, 100);
cof := func<f, nu | Coefficient(Components(f)[1*ZF], nu : InFunDomain:=false)>;

// ---- weight-2 basis y1,y2,y3 = Eisenstein (2) + cusp Omega (1) ----
M2sp := HMFSpace(Mgr, p31, [2,2]);
ybasis := EisensteinBasis(M2sp) cat CuspFormBasis(M2sp);       // y1,y2 Eis ; y3 = Omega
assert #ybasis eq 3;

// ---- the 6 quadrics y_i y_j span M_4 = Sym^2 M_2 ----
idx    := [<i,j> : j in [i..3], i in [1..3]];
quads  := [ybasis[p[1]]*ybasis[p[2]] : p in idx];
qnames := ["y" cat IntegerToString(p[1]) cat "*y" cat IntegerToString(p[2]) : p in idx];
nus := []; for nu -> a in Coefficients(Components(quads[1])[1*ZF]) do if not IsZero(nu) then Append(~nus, nu); end if; end for;
Sort(~nus, func<x,y|Trace(x)-Trace(y)>); nus := nus[1..30];
QC := Matrix(F, [[cof(q,nu) : q in quads] : nu in nus]);
assert Rank(QC) eq 6;                                          // M_4 = Sym^2 M_2, no relations
numin := [nu : nu in nus | ordval(nu) eq 1][1];

// ---- H^0(2K_Y): weight-4 CUSP forms with order >= 2 at both cusps, as quadrics ----
S4 := CuspFormBasis(HMFSpace(Mgr, p31, [4,4]));                // 4-dim, all p-new
S4quad := []; for f in S4 do ok,c := IsConsistent(Transpose(QC), Vector(F,[cof(f,nu):nu in nus])); assert ok; Append(~S4quad, c); end for;
// order >= 2 at both cusps: a_{nu_min}=0 at inf, and (Fricke W=-U_p/31 on S_4) at cusp 0
UpS := [HeckeOperator(f, p31) : f in S4];
condrows := [ [cof(S4[i], numin)      : i in [1..#S4]],        // cusp inf
              [-cof(UpS[i], numin)/31  : i in [1..#S4]] ];      // cusp 0
KerS := NullSpace(Transpose(Matrix(F, condrows)));
printf "dim H^0(2K_Y) = %o\n", Dimension(KerS);
assert Dimension(KerS) eq 2;
Fq := [ &+[Eltseq(d)[i]*S4quad[i] : i in [1..#S4]] : d in Basis(KerS) ];
printf "quadric basis: %o\n", qnames;
for q in Fq do printf "  pencil generator (coeffs in y_i y_j) = %o\n", Eltseq(q); end for;

// Omega^2 = y3^2 lies in the pencil
e6 := Vector(F, [0,0,0,0,0,1]);
assert e6 in sub<Universe(Fq)|Fq>;
printf "Omega^2 = y3^2 lies in the pencil: confirmed.\n";

// ---- degenerate members of the conic pencil ----
symmat := function(c) cc:=Eltseq(c);
  return Matrix(F,3,3,[cc[1],cc[2]/2,cc[3]/2, cc[2]/2,cc[4],cc[5]/2, cc[3]/2,cc[5]/2,cc[6]]);
end function;
M1 := symmat(Fq[1]); M2 := symmat(Fq[2]);
P<s,t> := PolynomialRing(F,2);
D := Determinant(s*ChangeRing(M1,P) + t*ChangeRing(M2,P));
printf "\ndiscriminant det(s*M1+t*M2) factors as:\n";
for fac in Factorization(D) do printf "  (%o)^%o\n", fac[1], fac[2]; end for;
printf "\nsingular fibres:\n";
for fac in Factorization(D) do
  cs := MonomialCoefficient(fac[1], s); ct := MonomialCoefficient(fac[1], t);
  if ct ne 0 then s0:=F!1; t0:=-cs/ct; else s0:=F!0; t0:=F!1; end if;
  r := Rank(s0*M1 + t0*M2);
  printf "  disc-multiplicity %o, conic rank %o : %o\n", fac[2], r,
    (r eq 1) select "DOUBLE LINE  ==>  multiple fibre 2*{Omega=0}" else "two lines (nodal fibre)";
end for;

print "";
print "CONCLUSION: the bicanonical pencil is a pencil of conics in P(M_2); its";
print "unique rank-1 member is Omega^2 = y3^2, so the multiplicity-2 multiple";
print "fibre of the elliptic fibration is 2*{Omega = 0} (zero locus of the";
print "weight-2 cusp form).";
exit;
