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
       
       // !! TODO : That only works if the intersection cycle is of 
       // length at least 3
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
intrinsic DoesCurveIntersectCusp(B::AlgMatElt, cusp::Pt, N::RngQuadIdl
				 : bound := 1000) -> BoolElt, SeqEnum[FldQuadElt]
{.}
  F := BaseRing(B);
  sigma := Automorphisms(F)[2];
  ZF := Integers(F);
  D := Discriminant(ZF);
  _<x> := PolynomialRing(F);
  sqrtD := Roots(x^2 - D)[2][1];
  a := B[1,1] / sqrtD;
  b := B[2,2] / sqrtD;
  lambda := B[1,2];
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
  I := N*(N + b * sqrtD*ZF); 
  ZF_mod_I := quo<ZF | I>;
  U, mU := UnitGroup(ZF_mod_I);
  // im_eps := sub<U | (ZF_mod_N!eps)@@mU, (-1)@@mU>;
  u_mod_I := ZF_mod_I!(-sigma(lambda)) div ZF_mod_I!z0;
  sunits, m_sunits := SUnitGroup(Norm(z0)*ZF);
  // We are looking for an s-unit u of norm 1 s.t. u equiv u_mod_I mod I
  gens := [sunits.i : i in [1..Ngens(sunits)]];
  // norm_gens := [Norm(m_sunits(g)) : g in gens]; 
  primes := [p[1] : p in Factorization(Norm(z0)*ZF)];
  // vecs := [[Valuation(F!n,p) : p in primes] cat [(1-Sign(n)) div 2] : n in norm_gens] cat [[0 : p in primes] cat [2]];
  // ker := Kernel(Matrix(vecs));
  // norm1_gens := [sunits!Eltseq(b)[1..Ngens(sunits)] : b in Basis(ker)];
  // norm1 := sub<sunits | norm1_gens>;
  val_mat := Matrix([[Valuation(m_sunits(g),p) : g in gens] : p in primes]);
  val_v0 := Vector([Minimum(Valuation(ZF!u_mod_I, p), Valuation(I,p)) 
		    : p in primes]);
  v0 := sunits!Eltseq(Solution(Transpose(val_mat), val_v0));
  I_primes := [p[1] : p in Factorization(I)];
  I_inv_vecs := Kernel(Transpose(Matrix([[Valuation(m_sunits(g), q) 
					  : g in gens] : q in I_primes])));
  I_inv := [sunits!Eltseq(b) : b in Basis(I_inv_vecs)];
  I_inv_sunits := sub<sunits | I_inv>;
  sunits_mod := hom<I_inv_sunits -> U | 
		   [(ZF_mod_I!m_sunits(t))@@mU : t in I_inv]>;
  v_mod_I := u_mod_I / ZF_mod_I!(m_sunits(v0));
  // If v0 kills all the valuation on I
  if (v_mod_I eq 0) then
      v_mod_I := 1;
  end if;
  sol_sunits := (v_mod_I@@mU)@@sunits_mod;
  nm := Norm(m_sunits(v0 + sol_sunits));
  ker_sunits_mod := Kernel(sunits_mod);
  ker_sunits_mod_gens := [ker_sunits_mod.i : i in [1..Ngens(ker_sunits_mod)]];
  norm_mod_gens := [Norm(m_sunits(sunits!g)) : g in ker_sunits_mod_gens];
  mod_vecs := [[Valuation(F!n,p) : p in primes] cat [(1-Sign(n)) div 2] :
	       n in norm_mod_gens] cat [[0 : p in primes] cat [2]];
  res := Vector([Valuation(F!nm,p) : p in primes] cat 
		[(1-Sign(nm)) div 2]);
  if res notin RowSpace(Matrix(mod_vecs)) then
      return false, [];
  end if;
  sol := Solution(Matrix(mod_vecs), res);
  ker_basis := Lattice(Matrix(Basis(Kernel(Matrix(mod_vecs)))));
  clv := [v[1] : v in CloseVectors(ker_basis, sol, bound)];
  sols := [sol - v : v in clv];
  vs := [m_sunits(sol_sunits-sunits!ker_sunits_mod!Eltseq(sol)[1..Degree(sol)-1]) : sol in sols];
  us := [v * m_sunits(v0) : v in vs];
  assert &and[ZF_mod_I!u eq u_mod_I : u in us];
  xs := [z0*u : u in us];
  assert &and[x + sigma(lambda) in I : x in xs];
  assert &and[Norm(x) eq Determinant(B) : x in xs];
  zs := [(x + sigma(lambda)) / (b*sqrtD) : x in xs];
  J := b*sqrtD*ZF div (N + b*sqrtD*ZF);
  lams := [];
  for z in zs do
      if (z eq 0) then
	  gamma11 := 1;
	  gamma21 := 0;
	  gamma22 := 1;
	  gamma12 := 0;
      else
	  gamma21 := Generators(z*J)[1];
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
      Append(~lams, B_new[1,2]);
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
       has_intersect, lambdas := DoesCurveIntersectCusp(B_cusp, cusp[2], N);
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
       assert &and[Ms[1] eq M : M in Ms];
       bases := [Matrix([Eltseq(x) : x in [A[i],A[i+1]]]) : i in [1..#s-1]];
       bases := [Matrix([Eltseq(x) : x in [F!1,A[1]]])] cat bases;
       cusp_mults := [0 : QF in QFs];
       for lambda in lambdas do
	   sols := [Solution(basis, Vector(Eltseq(F!lambda))) : basis in bases];
	   is_intersect := [Evaluate(QFs[i], 
				     Reverse(Eltseq(sols[i])))*Norm(Ms[i]) 
			    eq Norm(lambda) and sols[i][1] ge 0 and 
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
