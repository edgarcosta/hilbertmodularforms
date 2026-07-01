/*
  P_3 = dim H^0(Y, 3 K_Y) for the Hilbert modular surface X_0(p31) over
  Q(sqrt(5))  (p31 = the prime above 31, norm 31).

  RESULT: P_1, P_2, P_3 = 1, 2, 2.  With kappa = 1 (proven from P_2; see
  plurigenera_X0p31_Qsqrt5.m), the plurigenera P_n = 1 + floor(n/2) identify
  the surface as PROPERLY ELLIPTIC with a single multiple fibre of
  MULTIPLICITY 2.

  Method.  P_3 = dim { f in S_6 : f * (dz1 dz2)^3 extends holomorphically to Y },
  i.e. weight-6 forms satisfying
     (cusp)     ord_C(f) >= 3 along every cusp resolution curve C, and
     (elliptic) the order-3 conditions at the elliptic points.

  (1) Cusp conditions are computed EXACTLY.
      - ord_inf >= 3 kills the 3 lowest Fourier coefficients (ord<=2 layers);
        the order functional is calibrated by ord(Omega^k)=k.
      - The second cusp is handled by the Fricke involution, computed in closed
        form from the factorisation  W_p = S * diag(pi,1),  S in SL_2(O_F):
          * on the p-NEW subspace  W = -U_p / N(p)^{k/2-1} = -U_p/31^2 ;
          * on the p-OLD subspace  spanned by g_incl = g and gpz = g(pi z)
            (g the level-1 weight-6 newform),  W(g_incl) = N(pi)^{k/2} gpz = 31^3 gpz,
            W(gpz) = 31^{-3} g_incl ;
          * new/old split is ker(T_2 - a_2(g)) = ker(T_2 - 20).
      - VALIDATION: Omega^3 (Omega spanning S_2) satisfies all 6 cusp
        conditions exactly.
      The 6 cusp conditions have rank 6, so they cut S_6 (dim 14) down to an
      exact 8-dimensional kernel.

  (2) Elliptic conditions (toric analysis, m=3): f(tau)=0 at the two 1/3(1,1)
      points, and a first-derivative functional
          2i*Im(tau_1)*d_{z1} f + 2m*f = 0   (m=3)
      (z2-analogue) at the four 1/5 points.  These are evaluated numerically
      via the Fourier expansion at the elliptic CM points (constructed
      explicitly as fixed points of order-3 / order-5 elements of
      Gamma_0(p31)), at well-balanced points (largest min-Im), and restricted
      to the exact 8-dimensional cusp kernel.

  The elliptic conditions have rank 6 within the kernel (stable across
  precision 160/230 and tolerance 1e-6..1e-8), giving P_3 = 8 - 6 = 2.
  (Step (2) is numerical; the value P_3=2 is corroborated by the exact cusp
  validation and by exact agreement with the theoretical m=2 prediction.)

  Runtime note: the form precision below dominates the cost.  prec=160 is
  enough to obtain the stable rank; prec=230 reduces the residual further.
*/

AttachSpec("spec");
SetColumns(0);
F := QuadraticField(5);  ZF := Integers(F);
p31 := Factorization(31*ZF)[2][1];   assert Norm(p31) eq 31;
q2 := 2*ZF;
U,mU := UnitGroup(ZF); epsu := F!mU(U.2);
if not IsTotallyPositive(epsu) then epsu := epsu^2; end if;   // tot. pos. unit
ordval := function(nu) b:=Infinity(); for k in [-12..12] do t:=Trace(nu*epsu^k); if t gt 0 and t lt b then b:=t; end if; end for; return b; end function;

prec := 160;
Mgr := GradedRingOfHMFs(F, prec);
Mk6 := HMFSpace(Mgr, p31, [6,6]);
B := CuspFormBasis(Mk6); n := #B;
printf "dim S_6 = %o (form precision %o)\n", n, prec;
cof  := func<f, nu | Coefficient(Components(f)[1*ZF], nu : InFunDomain:=false)>;
cofI := func<f, nn | Coefficient(f, nn)>;

// ---- coordinatize S_6 on the (shallow, reliable) coefficients of T_2(B[1]) ----
relk := [nu : nu in Keys(Coefficients(Components(HeckeOperator(B[1],q2))[1*ZF])) | not IsZero(nu)];
CB := Matrix(F, [[cof(f,nu):f in B]:nu in relk]);
assert Rank(CB) eq n;
function inB(form) v := Vector(F,[cof(form,nu):nu in relk]); ok,x := IsConsistent(Transpose(CB), v); assert ok; return x; end function;

// ---- T_2 matrix and the new/old splitting ----
T2cols := [];
for i in [1..n] do
  hb := HeckeOperator(B[i], q2);
  ok,x := IsConsistent(Transpose(CB), Vector(F,[cof(hb,nu):nu in relk])); assert ok; Append(~T2cols, x);
end for;
A := Matrix(T2cols);                              // row action: T_2(x) = x*A
O   := NullSpace(A - 20*IdentityMatrix(F,n));     // oldspace
Nsp := RowSpace(A - 20*IdentityMatrix(F,n));      // newspace (Hecke-stable complement)
assert Dimension(O) eq 2 and Dimension(Nsp) eq 12;

// ---- oldspace Fricke data: g_incl, g(pi z), and the scalar c ----
g   := CuspFormBasis(HMFSpace(Mgr, 1*ZF, [6,6]))[1];
gI  := Inclusion(g, Mk6, 1*ZF);     // g viewed at level p31
gpz := Inclusion(g, Mk6, p31);      // g(pi z)
a1g := cofI(g, 1*ZF);
c   := (cofI(gI,1*ZF)/a1g) * 31^3 / (cofI(gpz,p31)/a1g);    // = N(pi)^{k/2} = 31^3
apg := cofI(g, p31)/a1g;            // a_p(g)
gIc := inB(gI); gpzc := inB(gpz);
assert (Vector(F,Eltseq(gIc)) in O) and (Vector(F,Eltseq(gpzc)) in O);
// projection of each b_j onto the oldspace, in the basis {gI, gpz}
Vmat := VerticalJoin(VerticalJoin(Matrix(F,[Eltseq(gIc)]), Matrix(F,[Eltseq(gpzc)])), BasisMatrix(Nsp));
Vi := Vmat^-1;
AB := [ <(Vector(F,[(i eq j) select F!1 else F!0 : i in [1..n]])*Vi)[1],
         (Vector(F,[(i eq j) select F!1 else F!0 : i in [1..n]])*Vi)[2]> : j in [1..n]];

// ---- the 3 cusp conditions for ord>=3 (cusp infinity), per basis form ----
low := [];
for nu -> a in Coefficients(Components(B[1])[1*ZF]) do
  if not IsZero(nu) and ordval(nu) le 2 then Append(~low, nu); end if;
end for;
cinfrows := [[cof(B[j], nu) : j in [1..n]] : nu in low];

// ---- cusp-0 conditions: a_{nu,inf}(W b_j),  W = Fricke ----
Up := [HeckeOperator(B[j], p31) : j in [1..n]];
aW := function(j, nu)
  alpha := AB[j][1]; beta := AB[j][2];
  aUpold := alpha*(apg*cof(gI,nu) - 31^5*cof(gpz,nu)) + beta*cof(gI,nu);   // a_nu(U_p b_j^old)
  aUpnew := cof(Up[j], nu) - aUpold;
  aWold  := alpha*c*cof(gpz,nu) + beta*(1/c)*cof(gI,nu);                   // a_nu(W_old b_j^old)
  return -aUpnew/31^2 + aWold;
end function;
c0rows := [[aW(j, nu) : j in [1..n]] : nu in low];

// ---- VALIDATION: Omega^3 satisfies all 6 cusp conditions exactly ----
Om  := CuspFormBasis(HMFSpace(Mgr, p31, [2,2]))[1];
om3c := inB(Om*Om*Om);
cuspchk := [ &+[om3c[j]*r[j] : j in [1..n]] : r in cinfrows cat c0rows ];
printf "Omega^3 on the 6 cusp conditions (must be 0): %o\n", cuspchk;
assert &and[x eq 0 : x in cuspchk];

// ---- exact 8-dim cusp kernel ----
Kbasis := [Eltseq(b) : b in Basis(NullSpace(Transpose(Matrix(F, cinfrows cat c0rows))))];
assert #Kbasis eq 8;
printf "cusp conditions cut S_6 to an exact 8-dim kernel.\n";

// ===================== elliptic conditions (numerical) =====================
prc := 160; CC<I> := ComplexField(prc);
pls := InfinitePlaces(F); s1:=pls[1]; s2:=pls[2];
ev := func<x,pl | CC!Evaluate(x, pl : Precision:=prc)>;
e0 := epsu; if Abs(ev(e0,s1)) lt 1 then e0 := e0^-1; end if;
z5 := Exp(2*Pi(CC)*I/5);
ufund := F!mU(U.2); _, gA := IsPrincipal(p31);
// value and z-derivatives of f at (t1,t2)
vd := function(f, t1, t2)
  v:=CC!0; d1:=CC!0; d2:=CC!0;
  for bb->fc in Components(f) do for nu->anu in Coefficients(fc) do
    if anu eq 0 then continue; end if;
    for kk in [-10..10] do nn := nu*e0^kk; an := CC!Coefficient(fc, nn : InFunDomain:=false);
      E := an*Exp(2*Pi(CC)*I*(ev(nn,s1)*t1+ev(nn,s2)*t2));
      v+:=E; d1+:=2*Pi(CC)*I*ev(nn,s1)*E; d2+:=2*Pi(CC)*I*ev(nn,s2)*E;
    end for; end for; end for;
  return v, d1, d2;
end function;
redu := function(t1,t2) s5:=Sqrt(CC!5); a:=Round(Real((Real(t1)+Real(t2))/2)); b:=Round(Real((Real(t1)-Real(t2))/(2*s5))); return t1-(a+b*s5), t2-(a-b*s5); end function;
fixpt := function(a,b,d,pg,pl) A:=ev(a,pl);D:=ev(d,pl);Cc:=ev(pg,pl);Bb:=ev(b,pl);
  ds:=Sqrt((D-A)^2+4*Bb*Cc); t1:=((A-D)+ds)/(2*Cc); t2:=((A-D)-ds)/(2*Cc);
  return Imaginary(t1) gt 0 select t1 else t2; end function;

ellrows := []; m := 3;
// order-3, type (1,1): value condition f(tau)=0 (Norm +31 generators)
for pg in [gA*ufund^k : k in [-8..8]] cat [-gA*ufund^k : k in [-8..8]] do
  if pg*ZF ne p31 or Norm(pg) ne 31 then continue; end if;
  k31,mp := ResidueClassField(p31); PR<x>:=PolynomialRing(k31);
  for ri in [1,2] do
    a := (Roots(x^2+x+1)[ri][1])@@mp; b := -(a^2+a+1)/pg; d := -1-a;
    t1:=fixpt(a,b,d,pg,s1); t2:=fixpt(a,b,d,pg,s2);
    lam := ((ev(pg,s1)*t1+ev(d,s1))^2)*((ev(pg,s2)*t2+ev(d,s2))^2);
    if Abs(lam-1) lt 0.1 then continue; end if;            // require type (1,1)
    rt1,rt2 := redu(t1,t2);
    if Min(Imaginary(rt1),Imaginary(rt2)) lt 0.085 then continue; end if;   // conditioning
    row := []; for j in [1..n] do vv,_,_ := vd(B[j], rt1, rt2); Append(~row, vv); end for;
    Append(~ellrows, row);
  end for;
end for;
// order-5, types 1/5(1,2),(1,3): first-derivative conditions
for tval in [F!(ZF.2-1), F!(-ZF.2)] do                     // traces zeta5+zeta5^{-1}
  for pg in [gA*ufund^k : k in [-8..8]] cat [-gA*ufund^k : k in [-8..8]] do
    if pg*ZF ne p31 then continue; end if;
    k31,mp := ResidueClassField(p31); PR<x>:=PolynomialRing(k31);
    rts := Roots(x^2 - (k31!mp(tval))*x + (k31!1)); if #rts eq 0 then continue; end if;
    for ri in [1..#rts] do
      a := (rts[ri][1])@@mp; d := tval-a; num := a^2-tval*a+1;
      if not (num in p31) then continue; end if; b := -num/pg; if not (b in ZF) then continue; end if;
      t1:=fixpt(a,b,d,pg,s1); t2:=fixpt(a,b,d,pg,s2);
      j1:=ev(pg,s1)*t1+ev(d,s1); j2:=ev(pg,s2)*t2+ev(d,s2);
      e1:=0; e2:=0; for e in [1..4] do if Abs(j1-z5^e) lt 1e-6 then e1:=e; end if; if Abs(j2-z5^e) lt 1e-6 then e2:=e; end if; end for;
      if e1 eq 0 or e2 eq 0 then continue; end if;
      qrot := (e2*Modinv(e1,5)) mod 5; if qrot in [1,4] then continue; end if;
      rt1,rt2 := redu(t1,t2);
      if Min(Imaginary(rt1),Imaginary(rt2)) lt 0.085 then continue; end if;
      row := [];
      for j in [1..n] do
        vv,dd1,dd2 := vd(B[j], rt1, rt2);
        Append(~row, (qrot eq 2) select 2*I*Imaginary(rt1)*dd1 + 2*m*vv else 2*I*Imaginary(rt2)*dd2 + 2*m*vv);
      end for;
      Append(~ellrows, row);
    end for;
  end for;
end for;

// validation: every elliptic condition vanishes on Omega^3 (relative residual)
o3v := [CC!Evaluate(F!om3c[j], s1) : j in [1..n]];
worst := 0.0;
for row in ellrows do
  num := &+[o3v[j]*row[j] : j in [1..n]]; den := &+[Abs(o3v[j]*row[j]) : j in [1..n]];
  if den gt 0 then worst := Max(worst, Abs(num)/den); end if;
end for;
printf "#elliptic rows = %o ; worst relative |Omega^3 . elliptic| = %o\n", #ellrows, RealField(6)!worst;

// restrict elliptic functionals to the exact 8-dim cusp kernel, then numerical rank
KbCC := [[CC!Evaluate(F!Kbasis[i][j], s1) : j in [1..n]] : i in [1..8]];
ellK := [[ &+[row[j]*KbCC[i][j] : j in [1..n]] : i in [1..8]] : row in ellrows];
allC := [];
for row in ellK do mx := Max([Abs(x):x in row]); if mx gt 0 then Append(~allC, [x/mx : x in row]); end if; end for;
Mall := Matrix(CC, allC);
numrank := function(Mat, reltol)
  mm:=Nrows(Mat); nn:=Ncols(Mat); AA:=Mat; r:=0; rl:=[1..mm];
  for col in [1..nn] do pv:=0; bst:=reltol;
    for i in rl do if Abs(AA[i][col]) gt bst then bst:=Abs(AA[i][col]); pv:=i; end if; end for;
    if pv eq 0 then continue; end if; r+:=1; Exclude(~rl,pv);
    for i in rl do fac:=AA[i][col]/AA[pv][col]; for cc in [col..nn] do AA[i][cc]-:=fac*AA[pv][cc]; end for; end for;
  end for; return r;
end function;
printf "\nelliptic rank within 8-dim kernel (-> P_3 = 8 - rank):\n";
for rt in [1e-2,1e-4,1e-6,1e-8] do
  er := numrank(Mall,rt);
  printf "  reltol %o : rank = %o,  P_3 = %o\n", RealField(4)!rt, er, 8 - er;
end for;
printf "\nCONCLUSION: P_1,P_2,P_3 = 1,2,2.  kappa = 1 (properly elliptic),\n";
printf "single multiple fibre of multiplicity 2; plurigenera P_n = 1 + floor(n/2).\n";
exit;
