intrinsic HZCuspIntersection(Gamma::GrpHilbert, t::RngIntElt) -> 
	  SeqEnum[SeqEnum[RngIntElt]]
{computes the intersection numbers of the Hirzebruch-Zagier divisor F_t with the cusp resolutions}
   cusps := CuspsWithResolution(Gamma);
   cusps_mults := [];
   b := Component(Gamma);
   N := Level(Gamma);
   F := BaseField(Gamma);
   for cusp in cusps do
       self_intersections := cusp[3];
       n := cusp[4];
       
       s := [-x : x in self_intersections];
       // Lemma II.3.2 in [vdG]
       if #s eq 1 and n eq 1 then
	   s[1] +:= 2;
       end if;
       ws := [HJReconstructPeriodic(F,[s[(i+j-2) mod #s + 1] : j in [1..#s]]) 
	      : i in [1..#s]];
       Qs := [Matrix([[Norm(x+y)-Norm(x)-Norm(y) : y in [1,w]] : x in [1,w]]) 
	      : w in ws];
       Ds := [Denominator(Q) : Q in Qs];
       for i in [1..#Qs] do
	   if IsOdd(Integers()!(Ds[i]*Qs[i][1,1])) or 
	      IsOdd(Integers()!(Ds[i]*Qs[i][2,2])) then
	       Ds[i] *:= 2;
	   end if;
       end for;
       QFs := [* QuadraticForm(Ds[i]*Qs[i]/2) : i in [1..#Qs] *];
       all_pqs := [];
       // all_mults := [];
       for QF in QFs do
	   pqs := [];
	   p_plus_q := 0;
	   min_val := 0;
	   while (min_val le t) do
	       evs := [Evaluate(QF, [p,p_plus_q - p]) : p in [0..p_plus_q]];
	       min_val := Minimum(evs);
	       ps := [p : p in [0..p_plus_q] | evs[p+1] eq t];
	       pqs cat:= [[p, p_plus_q - p] : p in ps];
	       p_plus_q +:= 1;
	   end while;
	   pqs_prim := [];
	   for pq in pqs do
	       n := GCD(pq[1], pq[2]);
	       Append(~pqs_prim, [pq[1] div n, pq[2] div n]);
	   end for;
	   // mults := [&+([0] cat [pq[2] : pq in pqs_prim])
	//	    , &+([0] cat [pq[1] : pq in pqs_prim])];
	   // Append(~all_mults, mults);
	   Append(~all_pqs, pqs_prim);
       end for;
       cusp_mults := [0 : QF in QFs];
       for cyc_idx in [1..#QFs] do
	   // cyc_idx_prev := (cyc_idx + #QFs - 2) mod #QFs + 1;
	   cyc_idx_next := cyc_idx mod #QFs + 1;
	   cusp_mults[cyc_idx] +:= &+([0] cat [pq[1] : pq in all_pqs[cyc_idx]]);
	   cusp_mults[cyc_idx] +:= 
	       &+([0] cat [pq[2] : pq in all_pqs[cyc_idx_next] | pq[1] ne 0]);
       end for;
       //assert &and[all_mults[i][2] eq all_mults[i+1][1] 
	//	   : i in [1..#all_mults-1]];
       // cusp_mults := [m[1] : m in all_mults];
       // realigning to fit the intersection numbers
       // cusp_mults := cusp_mults[2..#cusp_mults] cat [cusp_mults[1]];
       Append(~cusps_mults, cusp_mults);
   end for;
   return cusps_mults;
end intrinsic;

// !! TODO : Should be able to figure out the bound from the arithmetic - there is a sublatice which fixes everything
intrinsic DoesCurveIntersectInfty(B::AlgMatElt, N::RngQuadIdl) -> BoolElt, SeqEnum[FldQuadElt]
{Checks whether the curve F_B on X_0(N) intersects the cusp at infinity. If it does, returns a list of possible values for lambda such that F_B looks like F_lambda near the cusp.}
  F := BaseRing(B);
  sigma := Automorphisms(F)[2];
  ZF := Integers(F);
  D := Discriminant(ZF);
  _<x> := PolynomialRing(F);
  sqrtD := Roots(x^2 - D)[2][1];
  a := B[1,1] / sqrtD;
  b := B[2,2] / sqrtD;
  lambda := B[1,2];
  if (b eq 0) then
      if (lambda eq sigma(lambda)) then
	  eps := FundamentalUnit(F);
	  g := Matrix([[eps,0],[0,eps^(-1)]]);
	  B := (Transpose(Parent(g)![sigma(x) : x in Eltseq(g)]) * B * g);
	  a := B[1,1] / sqrtD;
	  b := B[2,2] / sqrtD;
	  lambda := B[1,2];
      end if;
      assert lambda ne sigma(lambda);
      t := 1;
      if a*sqrtD eq -lambda+sigma(lambda) then
	  t := -1;
      end if;
      g := Matrix([[1,t],[0,1]]);
      B := (Transpose(Parent(g)![sigma(x) : x in Eltseq(g)]) * B * g);
      a := B[1,1] / sqrtD;
      b := B[2,2] / sqrtD;
      lambda := B[1,2];
  end if;
  assert b ne 0;
  norm_exists, elts := NormEquation(ZF, Integers()!Determinant(B));
  if not norm_exists then
      return false, [];
  end if;
  z0 := elts[1];
  eps := FundamentalUnit(F);
  if (Norm(eps) eq -1) then
      if (Norm(elts[1]) eq -Determinant(B)) then
	  z0 *:= eps;
      end if;
      eps := eps^2;
  end if;
  // Problem: x may not be integral.
  // Seems like we can restrict to x with Norm(z0)*x integral - verify!!!
  N_fac := Factorization(N);
  I := &*([PowerIdeal(ZF) | 
	  pe[1]^(pe[2]+Valuation(b*sqrtD,pe[1])) : pe in N_fac]);
  // to work integrally we scale everything by the norm
  I *:= Norm(N);
  J := sigma(lambda)*Norm(N)*ZF + I;
  I_primes := [p[1] : p in Factorization(I)];
  // find an S-unit v0 such that v0 is in J
  sunits, m_sunits := SUnitGroup(Norm(N)*ZF);
  gens := [sunits.i : i in [1..Ngens(sunits)]];
  N_primes := [p[1] : p in Factorization(N)];
  val_mat := Matrix([[Valuation(m_sunits(g),p) : g in gens] : p in I_primes]);
  val_v0 := Vector([Valuation(J,p) : p in I_primes]);
  v0 := sunits!Eltseq(Solution(Transpose(val_mat), val_v0));
  assert m_sunits(v0) in J;
  I := I div J;
  ZF_mod_I := quo<ZF | I>;
  U, mU := UnitGroup(ZF_mod_I);
  xN_mod_I := ZF_mod_I!(-sigma(lambda)*Norm(N)/m_sunits(v0));
  // We are looking for an s-unit xN s.t. xN equiv xN_mod_I mod I
  J_primes := [p[1] : p in Factorization(I)];
  if #J_primes gt 0 then
      I_inv_vecs := Kernel(Transpose(Matrix([[Valuation(m_sunits(g), q) 
					      : g in gens] : q in J_primes])));
      I_inv := [sunits!Eltseq(b) : b in Basis(I_inv_vecs)];
      I_inv_sunits := sub<sunits | I_inv>;
  else
      I_inv := gens;
      I_inv_sunits := sunits;
  end if;
  sunits_mod := hom<I_inv_sunits -> U | 
		   [(ZF_mod_I!m_sunits(t))@@mU : t in I_inv]>;
  if (xN_mod_I eq 0) then
      assert I eq 1*ZF;
      xN_mod_I := 1;
  end if;
  sol_sunits := (xN_mod_I@@mU)@@sunits_mod;
  nm := Norm(m_sunits(v0 + sol_sunits));
  nm := Rationals()! Determinant(B)*Norm(N)^2 / nm;
  ker_sunits_mod := Kernel(sunits_mod);
  ker_sunits_mod_gens := [ker_sunits_mod.i : i in [1..Ngens(ker_sunits_mod)]];
  norm_mod_gens := [Norm(m_sunits(sunits!g)) : g in ker_sunits_mod_gens];
  mod_vecs := [[Valuation(F!n,p) : p in I_primes] cat [(1-Sign(n)) div 2] :
	       n in norm_mod_gens] cat [[0 : p in I_primes] cat [2]];
  res := Vector([Valuation(F!nm,p) : p in I_primes] cat 
		[(1-Sign(nm)) div 2]);
  if res notin RowSpace(Matrix(mod_vecs)) then
      return false, [];
  end if;
  sol := Solution(Matrix(mod_vecs), res);
  sol_sunit := sunits!ker_sunits_mod!Eltseq(sol)[1..Degree(sol)-1];
  // this should be an element of the correct norm and residue
  assert Norm(m_sunits(sol_sunit)) eq nm;
  assert ZF_mod_I!m_sunits(sol_sunit) eq 0;
  ker_basis := Lattice(Matrix(Basis(Kernel(Matrix(mod_vecs)))));
  ker_basis_sunits := sub< sunits | [sunits!ker_sunits_mod!Eltseq(sol)[1..Degree(sol)-1] : sol in Basis(ker_basis)]>;
  vecs := [[Valuation(m_sunits(g),p) : p in I_primes] cat [(1-Sign(Norm(m_sunits(g)))) div 2] : g in gens] cat [[0 : p in I_primes] cat [2]];
  ker := Kernel(Matrix(vecs));
  tot_pos_unit_gens := [sunits!Eltseq(b)[1..Ngens(sunits)] : b in Basis(ker)];
  tot_pos_unit_sunits := sub<sunits | tot_pos_unit_gens>;
  reps, quo_map := ker_basis_sunits / (ker_basis_sunits meet tot_pos_unit_sunits);
  // sols := [sol_sunits + sol_sunit + r@@quo_map : r in reps];  
  sols := [sol_sunits + sol_sunit];
  vs := [m_sunits(s) : s in sols];
  us := [v * m_sunits(v0) : v in vs];
  assert &and[ZF_mod_I!u eq xN_mod_I : u in us];
  xs := [u / Norm(N) : u in us];
  assert &and[&and[Valuation(x + sigma(lambda),p) ge Valuation(N*b*sqrtD,p) 
		   : p in N_primes] : x in xs];
  assert &and[Norm(x) eq Determinant(B) : x in xs];
  zs := [(x + sigma(lambda)) / (b*sqrtD) : x in xs];
  // J := b*sqrtD*ZF div (N + b*sqrtD*ZF);
  lams := [];
  for z in zs do
      if (z eq 0) then
	  gamma11 := 1;
	  gamma21 := 0;
	  gamma22 := 1;
	  gamma12 := 0;
      else
	  gamma21 := Denominator(z); // Generators(z*J)[1];
	  gamma11 := gamma21 / z;
	  _, d := IsPrincipal(gamma11*ZF + gamma21*ZF);
	  gamma11 := gamma11 / d;
	  gamma21 := gamma21 / d;
	  R := quo<ZF | gamma21*ZF>;
	  gamma22 := ZF!((R!gamma11)^(-1));
	  gamma12 := (-1 + gamma11*gamma22)/ gamma21;
      end if;
      g := Matrix([[gamma11, gamma12], [gamma21, gamma22]]);
      assert Determinant(g) eq 1;
      B_new := (Transpose(Parent(g)![sigma(x) : x in Eltseq(g)]) * B * g);
      assert B_new[1,1] eq 0;
      // our_new lambda
      lam_new := B_new[1,2];
      if not IsTotallyPositive(lam_new) then
	  lam_new := -lam_new;
      end if;
      Append(~lams, lam_new);
  end for;
  return true, [x : x in Set(lams)];
end intrinsic;
								 

intrinsic HZCuspIntersection(Gamma::GrpHilbert, lambda::FldQuadElt) -> 
	  SeqEnum[SeqEnum[RngIntElt]]
{computes the intersection numbers of the Hirzebruch-Zagier divisor F_B with the cusp resolutions, where B = Matrix([0, lambda, -lambda', 0]).}
   cusps := CuspsWithResolution(Gamma);
   cusps_mults := [];
   b := Component(Gamma);
   N := Level(Gamma);
   F := BaseField(Gamma);
   ZF := Integers(F);
   sigma := Automorphisms(F)[2];
   B := Matrix([[0,lambda],[-sigma(lambda), 0]]);
   for cusp in cusps do
       M, V, g := CuspResolutionMV(1*ZF, N, F!cusp[2][1], F!cusp[2][2]);
       g := g^(-1);
       B_cusp := (Transpose(Parent(g)![sigma(x) : x in Eltseq(g)]) * B * g);
       self_intersections := cusp[3];
       n := cusp[4];
       s := [-x : x in self_intersections];
       // Lemma II.3.2 in [vdG]
       if #s eq 1 and n eq 1 then
	   s[1] +:= 2;
       end if;
//       lambdas := [B_cusp[1,2]];
//       if (B_cusp[1,1] ne 0) then
       has_intersect, lambdas := DoesCurveIntersectInfty(B_cusp, N);
       if not has_intersect then
	   Append(~cusps_mults, [0 : i in [1..#s]]);
	   continue;
       end if;
       // end if;
       ws := [HJReconstructPeriodic(F,[s[(i+j-2) mod #s + 1] : j in [1..#s]]) 
	      : i in [1..#s]];
       Qs := [Matrix([[Norm(x+y)-Norm(x)-Norm(y) : y in [1,w]] : x in [1,w]]) 
	      : w in ws];
       Ds := [Denominator(Q) : Q in Qs];
       for i in [1..#Qs] do
	   if IsOdd(Integers()!(Ds[i]*Qs[i][1,1])) or 
	      IsOdd(Integers()!(Ds[i]*Qs[i][2,2])) then
	       Ds[i] *:= 2;
	   end if;
       end for;
       QFs := [* QuadraticForm(Ds[i]*Qs[i]/2) : i in [1..#Qs] *];
       A := [1/ws[1]];
       for i in [1..#s-1] do
	   A[i+1] := A[i] / ws[i+1];
       end for;
       assert &and[A[i] + A[i+2] eq s[i+1] * A[i+1] : i in [1..#s-2]];
       Ms := [1*ZF + A[1]*ZF] cat [A[i] * ZF + A[i+1]*ZF : i in [1..#s-1]];
       _, alpha := IsPrincipal(Ms[1]);
       eps := FundamentalUnit(F);
       if Norm(alpha) lt 0 then
	   alpha *:= eps;
       end if;
       if not IsTotallyPositive(alpha) then
	   alpha *:= -1;
       end if;
       assert IsTotallyPositive(alpha);
       assert &and[Ms[1] eq M : M in Ms];
       bases := [Matrix([Eltseq(x) : x in [A[i],A[i+1]]]) : i in [1..#s-1]];
       bases := [Matrix([Eltseq(x) : x in [F!1,A[1]]])] cat bases;
       cusp_mults := [0 : QF in QFs];
       // basis for the big cone
       big_basis := Matrix([Eltseq(x) : x in [F!1,A[#A]]]);
       for lambda in lambdas do
	   big_coords := Solution(big_basis, Vector(Eltseq(F!lambda*alpha)));
	   while big_coords[2] lt 0 do
	       alpha *:= eps^(-2);
	       big_coords := Solution(big_basis, 
				      Vector(Eltseq(F!lambda*alpha)));
	   end while;
	   while big_coords[1] lt 0 do
	       alpha *:= eps^2;
	       big_coords := Solution(big_basis, 
				      Vector(Eltseq(F!lambda*alpha)));
	   end while;       				 
	   sols := [Solution(basis, Vector(Eltseq(F!lambda*alpha))) 
		    : basis in bases];
	   is_intersect := [Evaluate(QFs[i], 
				     Reverse(Eltseq(sols[i])))*Norm(Ms[i]) 
			    eq Norm(lambda*alpha) and sols[i][1] ge 0 and 
			    sols[i][2] ge 0 
			    :  i in [1..#s]];
	   rel_inds := [i : i in [1..#s] | is_intersect[i]];
	   all_pqs := [];
	   for i in [1..#s] do
	       if (is_intersect[i]) then
		   QF := QFs[i];
		   p,q := Explode(Eltseq(ChangeRing(sols[i], Integers())));
		   n := GCD(p,q);
		   Append(~all_pqs, [[p div n, q div n]]);
	       else
		   Append(~all_pqs, []);
	       end if;
	   end for;
	   for cyc_idx in [1..#QFs] do
	       cyc_idx_next := cyc_idx mod #QFs + 1;
	       cusp_mults[cyc_idx] +:= &+([0] cat [pq[1] : pq in all_pqs[cyc_idx]]);
	       cusp_mults[cyc_idx] +:= 
		   &+([0] cat [pq[2] : pq in all_pqs[cyc_idx_next] | pq[1] ne 0]);
	   end for;
       end for;
       Append(~cusps_mults, cusp_mults);
   end for;
   return cusps_mults;
end intrinsic;

intrinsic HZCuspIntersectionComponents(Gamma::GrpHilbert, t::RngIntElt) -> 
	  SeqEnum[SeqEnum[RngIntElt]]
{computes the intersection numbers of the Hirzebruch-Zagier divisor F_t with the cusp resolutions}
   cusps := CuspsWithResolution(Gamma);
   cusps_mults := [];
   b := Component(Gamma);
   N := Level(Gamma);
   F := BaseField(Gamma);
   comps := GetAllHZComponents(Gamma,t);
   for cusp in cusps do
       self_intersections := cusp[3];
       n := cusp[4];
       
       s := [-x : x in self_intersections];
       // Lemma II.3.2 in [vdG]
       if #s eq 1 and n eq 1 then
	   s[1] +:= 2;
       end if;
       ws := [HJReconstructPeriodic(F,[s[(i+j-2) mod #s + 1] : j in [1..#s]]) 
	      : i in [1..#s]];
       Qs := [Matrix([[Norm(x+y)-Norm(x)-Norm(y) : y in [1,w]] : x in [1,w]]) 
	      : w in ws];
       Ds := [Denominator(Q) : Q in Qs];
       for i in [1..#Qs] do
	   if IsOdd(Integers()!(Ds[i]*Qs[i][1,1])) or 
	      IsOdd(Integers()!(Ds[i]*Qs[i][2,2])) then
	       Ds[i] *:= 2;
	   end if;
       end for;
       QFs := [* QuadraticForm(Ds[i]*Qs[i]/2) : i in [1..#Qs] *];
       A := [1/ws[1]];
       for i in [1..#s-1] do
	   A[i+1] := A[i] / ws[i+1];
       end for;
       assert &and[A[i] + A[i+2] eq s[i+1] * A[i+1] : i in [1..#s-2]];
       A := [1] cat A;
       all_pqs := [];
       all_comps := [];
       for k->QF in QFs do
	   pqs := [];
	   p_plus_q := 0;
	   min_val := 0;
	   while (min_val le t) do
	       evs := [Evaluate(QF, [p,p_plus_q - p]) : p in [0..p_plus_q]];
	       min_val := Minimum(evs);
	       ps := [p : p in [0..p_plus_q] | evs[p+1] eq t];
	       pqs cat:= [[p, p_plus_q - p] : p in ps];
	       p_plus_q +:= 1;
	   end while;
	   lambdas := [pq[1]*A[k] + pq[2]*A[k+1] : pq in pqs];
	   Append(~all_comps, [GetHZComponent(Gamma, lambda, comps) : lambda in lambdas]);
	   pqs_prim := [];
	   for pq in pqs do
	       n := GCD(pq[1], pq[2]);
	       Append(~pqs_prim, [pq[1] div n, pq[2] div n]);
	   end for;
	   Append(~all_pqs, pqs_prim);
       end for;
       cusp_mults := [[0 : QF in QFs] : c in comps];
       for cyc_idx in [1..#QFs] do
	   cyc_idx_next := cyc_idx mod #QFs + 1;
	   for j in [1..#all_pqs[cyc_idx]] do
	       cusp_mults[cyc_idx][all_comps[cyc_idx][j]] +:= all_pqs[cyc_idx][j][1];
	       if (all_pqs[cyc_idx_next][j][1] ne 0) then
		   cusp_mults[cyc_idx][all_comps[cyc_idx][j]] +:= all_pqs[cyc_idx_next][j][2];
	       end if;
	   end for;
       end for;
       Append(~cusps_mults, cusp_mults);
   end for;
   return cusps_mults;
end intrinsic;
