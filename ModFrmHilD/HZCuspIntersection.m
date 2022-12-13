intrinsic HZCuspIntersection(F::FldQuad, t::RngIntElt, 
			     N::RngOrdIdl, b::RngOrdIdl 
			     : GammaType := "Gamma0") -> 
	  SeqEnum[SeqEnum[RngIntElt]]
{computes the intersection numbers of the Hirzebruch-Zagier divisor F_t with the cusp resolutions}
   cusps := Cusps(N, b : GammaType := GammaType);
   cusps_mults := [];
   for cusp in cusps do
       alpha := cusp[3][1];
       beta := cusp[3][2];
       self_intersections := CuspResolutionIntersections(F, b, N, alpha, beta);
       // !! TODO : That only works if the intersection cycle is of 
       // length at least 3
       s := [-x : x in self_intersections];
       ws := [HJReconstructPeriodic(F,[s[(i+j) mod #s + 1] : j in [1..#s]]) 
	      : i in [1..#s]];
       Qs := [Matrix([[Norm(x+y)-Norm(x)-Norm(y) : y in [1,w]] : x in [1,w]]) 
	      : w in ws];
       QFs := [* QuadraticForm(Denominator(Q)*Q/2) : Q in Qs *];
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
       Append(~cusps_mults, cusp_mults);
   end for;
   return cusps_mults;
end intrinsic;
