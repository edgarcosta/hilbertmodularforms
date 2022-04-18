freeze;

///////////////////////////////////////////////////////////////////////////
// Projective line of a RngOrdRes, and orbits under matrix group action. //
//                                                                       // 
// Steve Donnelly                                                        //
// New version November 2011                                             //
///////////////////////////////////////////////////////////////////////////

// TO DO: for consistency, add option in the RngInt case for the
//        P1 elements to be vectors over Integers() not Integers(N)
//        (the vararg would appear in both intrinsics)

debug := false;

///////////////////////////////////////////////////////////////////////////
// Routine to list elements of a quotient ring
///////////////////////////////////////////////////////////////////////////

// cardinality of (R/I)*

function EulerPhi(I)
   phi := 1;
   for tup in Factorization(I) do 
      NP := AbsoluteNorm(tup[1]);
      phi *:= (NP-1) * NP^(tup[2]-1);
   end for;
   return phi;
end function;

// cardinality of P^1(R/I)

function EulerPsi(I)
   phi := 1;
   for tup in Factorization(I) do 
      NP := AbsoluteNorm(tup[1]);
      phi *:= (NP+1) * NP^(tup[2]-1);
   end for;
   return phi;
end function;

// Given a proper ideal I in an absolute order O, return
// [b_1, .., b_d] in O and integers [n_1, .., n_d] such that
// { sum over 1<=i<=d of x_i*b_i : 0 <= x_i < n_i } forms a
// system of residue class representatives for O/I

function residue_class_reps(I)

  O := Order(I);
  d := Degree(O);
  bas := [O!b : b in Basis(O)];
  assert #bas eq d and bas[1] eq 1;
  Zd := RowSpace(IdentityMatrix(Integers(),d));

  fact := Factorization(Minimum(I));
  if #fact eq 0 then
    return bas, [1 : i in [1..d]]; end if;

  ns := [1 : i in [1..d]];
  for tup in fact do
    p, M := Explode(tup);
    // Choose 1 = b1, .., bd (a permutation of bas) such that for all 0 < m <= M,
    // a basis of O/(I+p^m) is given by b1, .., bl for some l.
    bs_p := [];
    ns_p := [];
    for m := M to 1 by -1 do
      Im := BasisMatrix( I + p^m*O );
      Im1 := BasisMatrix( I + p^(m-1)*O );
      k := Valuation(Determinant(Im), p) - Valuation(Determinant(Im1), p) - #bs_p;
      // Need k generators at level m
      if k eq 0 then continue m; end if;
      ns_p cat:= [p^m : i in [1..k]];
      S := sub< Zd | [Im[n]: n in [1..Nrows(Im)]] cat [Zd! Eltseq(p^(m-1)*b) : b in bs_p] >;
      Sm1 := sub< Zd | [Im1[n]: n in [1..Nrows(Im1)]] >;
      for b in bas do
        if b notin bs_p then
          v := Eltseq( p^(m-1)*b );
        //Include(~S, Zd!v, ~new); // TO DO: bug!! this always gives true
          S, new := Include(S, Zd!v);
          if new then
            Append(~bs_p, b);
            k -:= 1;
            if k eq 0 then break b; end if;
          end if;
        end if;
      end for;
    end for;
    // assert S eq Sm1;
    assert #bs_p eq #ns_p;
    if #bs_p lt d then
      bs_p cat:= [b : b in bas | b notin bs_p];
      ns_p cat:= [1 : i in [1+#ns_p..d]];
    end if;
    perm := [Index(bs_p, b) : b in bas];
    ns := [ns[i] * ns_p[ii] where ii is perm[i] : i in [1..d]];
  end for;

  assert ns[1] eq Minimum(I);

  if debug then
    reps := [0];
    for i := 1 to d do
      reps := [ r + x*bas[i] : r in reps, x in [0..ns[i]-1] ];
    end for;
    assert #reps eq Norm(I);
    assert #{r @ modI : r in reps} eq Norm(I) where _, modI := quo<O|I>;
  end if;

  return bas, ns;
end function;

intrinsic Elements(R::RngOrdRes) -> SeqEnum
{Given a quotient ring R of an order O of some number field, returns 
 a sequence containing representatives in O of the elements of R
 (sorted in a standard order)} 

   I := Modulus(R);
   OI := Order(I);
   bs, ns := residue_class_reps(I);
   elts := [R| 0];
   for i := 1 to #bs do 
      bi := R! bs[i];
      elts_i := [R| x*bi : x in [0..ns[i]-1] ];
      elts := [e + ei : e in elts, ei in elts_i];
   end for;
   ChangeUniverse(~elts, OI);
   Sort(~elts);
   assert #elts eq AbsoluteNorm(I);
   return elts;
end intrinsic;

function get_residues(O, R)
   res := ChangeUniverse(Elements(R), O);
   if debug then
      I := Modulus(R);
      for r in res do
         assert r eq r mod I;
      end for;
   end if;
   return res;
end function;

/////////////////////////////////////////////////////////////////////
// Projective line
/////////////////////////////////////////////////////////////////////

intrinsic ProjectiveLine(R::RngOrdRes : Type:="Vector") 
       -> SetIndx, UserProgram

{Given a quotient ring R of an order O of some number field, returns 
an indexed set containing standard representatives [u,v] for P1(R), 
where u and v belong to O.  Also returns a function which identifies
the standard representative of any given element [u',v'] in P1(R)}

   require Type cmpeq "Vector" or Type cmpeq "Matrix": 
     "The optional argument 'Type' should be \"Vector\" or \"Matrix\"";

   I := Modulus(R);
   O := Order(I);
   require IsAbsoluteOrder(O) : "Not implemented for relative fields";

   zero := O!0;
   one := O!1;

   if Minimum(I) eq 1 then 

        case Type:
           when "Vector":   p1 := Vector([O|0,1]);
           when "Matrix":   p1 := Matrix(1, [O|0,1]);
        end case;

        P1 := {@ p1 @};

        function P1rep(x, check, scaling)
           return true, p1, one;
        end function;

   elif IsPrime(I) then  // TO DO: use finite field

        res := get_residues(O, R);

        T := AssociativeArray();
        for r in Exclude(res, zero) do
           T[r] := Modinv(r,I);
        end for;

        case Type: when "Vector":

            P1 := {@ Vector([O|0,1]) @} join {@ Vector([O|1,r]) : r in res @};
 
            function P1rep(x, check, scaling)
               u0 := x[1] mod I;
               if IsZero(u0) then
                  if check and x[2] in I then
                     return false, _, _;
                  end if;
                  s := Modinv(x[2], I);
                  return true, Vector([O|0,1]), s;
               else
                  s := T[u0];
                  v := (s*x[2]) mod I;
                  return true, Vector([O|1,v]), s;
               end if;
            end function;
 
        when "Matrix":

            P1 := {@ Matrix(1, [O|0,1]) @} join {@ Matrix(1, [O|1,r]) : r in res @};
 
            function P1rep(x, check, scaling)
               u0 := x[1,1] mod I;
               if IsZero(u0) then
                  if check and x[2,1] in I then
                     return false, _, _;
                  end if;
                  s := Modinv(x[2,1], I);
                  return true, Matrix(1, [O|0,1]), s;
               else
                  s := T[u0];
                  v := (s*x[2,1]) mod I;
                  return true, Matrix(1, [O|1,v]), s;
               end if;
            end function;
 
        end case;

   else // I is not (1) and not prime

        res := get_residues(O, R);
        resI := {r : r in res | Minimum(I+r*O) eq 1};
        pairsI := {<r,Modinv(r,I)> : r in resI};

        T := AssociativeArray();
        V := AssociativeArray();

        FI := Factorization(I);
        Ps := [t[1] : t in FI];
        Ivals := [t[2] : t in FI];

        Ds := Divisors(I);
        Exclude(~Ds, I);
        Exclude(~Ds, 1*O);
        Sort(~Ds);
        Reverse(~Ds);

        // For each divisor D, deal with the elements [d,v] where (d) = D
        // Here the v are representatives mod I/D chosen so (D,v) = (1)
        // Tables:
        //     T[u] = <s, d, I/D> such that s*u = d
        //     V[[d,v]] = [d,v'] such that (d,v',I) = (1)
        // The keys u and v are elements of res, ie reduced reps mod I
        // For each d, [d,v] is in Keys(V) iff v = v' mod I for some v' 
        // with (d,v',I) = (1).  (We could do this mod I/D instead, 
        // which would be enough to retrieve reps for true input, 
        // but this way the result of the check is also stored.)

        // First deal with D = (0)
        x := [O|zero,one]; 
        P1 := {@ x @};
        V0 := AssociativeArray();
        for rs in pairsI do
           r, s := Explode(rs);
           V0[r] := <x, s>;
        end for;
        V[zero] := V0;
        T[zero] := <one, zero, 1*O>;

        for D in Ds do
           Dvals := [Valuation(D,P) : P in Ps];
           // choose d such that D = (d) + I
           d := O! Minimum(D);
           if d*O + I ne D then
              d := WeakApproximation(Ps, Dvals);
           end if;
           d := (O!d) mod I;
           assert d*O + I eq D;
           D1 := O !! (I/D);
           DD1 := D + D1;
           res1 := Seqset(get_residues(O, quo<O|D1>));
           if Minimum(DD1) ne 1 then
              res1 := {r : r in res1 | Minimum(DD1+r*O) eq 1};
           end if;
           pairsI_1modD1 := {rs : rs in pairsI | rs[1] mod D1 eq one};
           assert one mod D1 eq one;

           // List elements [d,v], and choose v' to be v mod D1 where possible
           Vd := AssociativeArray();
           tricky := [i : i in [1..#Ps] | Dvals[i] eq Ivals[i]];
           easy := IsEmpty(tricky); // v' = v mod D1 works for all valid [d,v]
           for v0 in res1 do
              v := v0;
              if not easy then
                 // Notes:
                 // (1) To get reps with (d,v) coprime, use d*O instead of D here. 
                 // (2) It's not easy to give a natural deterministic rule for this.
                 //  So we don't insist ProjectiveLine chooses the same reps each time 
                 //  it's called; of course each returned function P1rep must do so
                 while Minimum(D+v*O) ne 1 do 
                    v +:= Random(Basis(D1));
                 end while;
              end if;
              x := [O|d,v]; 
              Include(~P1, x);
              for rs in pairsI_1modD1 do // TO DO: entries get assigned multiple times
                 // r = 1 (mod D1)  ==>  r*d = d (mod I)
                 r, s := Explode(rs);
                 rv := (r*v) mod I;
                 Vd[rv] := <x, s>; 
              end for;
           end for;
           V[d] := Vd;

           // Set up table T: need an entry for each r mod D1
           num := EulerPhi(D1);
           entries := {O| };
           for rs in pairsI do
              r, s := Explode(rs);
              r1 := r mod D1;
              if r1 notin entries then
                 Include(~entries, r1);
                 u := (r*d) mod I;
                 T[u] := <s, d, D1>;
                 if #entries eq num then
                    break;
                 end if;
              end if;
           end for;
        end for;

        // Finally deal with D = (1)
        V1 := AssociativeArray();
        for r in res do
           x := [O|one,r];
           Include(~P1, x);
           V1[r] := <x, one>;
        end for;
        V[one] := V1;
        for rs in pairsI do
           r, s := Explode(rs);
           T[r] := <s, one, I>;
        end for;

        assert #P1 eq EulerPsi(I);
        assert #Keys(T) eq Norm(I);

        if Type eq "Vector" then

            P1 := {@ Vector(x) : x in P1 @};
 
            VV := AssociativeArray();
            for d in Keys(V) do
               Vd := V[d];
               VVd := AssociativeArray();
               for r in Keys(Vd) do
                  Vdr := Vd[r];
                  VVd[r] := <Vector(Vdr[1]), Vdr[2]>;
               end for;
               VV[d] := VVd;
            end for;
            V := VV;

        end if;
        if Type eq "Vector" then

            function P1rep(x0, check, scaling)
               u0 := x0[1] mod I;
               s, u, D1 := Explode(T[u0]);
               v := (s*x0[2]) mod I;
               b, t := IsDefined(V[u], v);
               if b then
                  if scaling then
                     return true, t[1], s*t[2];
                  else
                     return true, t[1], _;
                  end if;
               else
                  return false, _, _;
               end if;
            end function;
 
        elif Type eq "Matrix" then

            P1 := {@ Matrix(1, x) : x in P1 @};
 
            VV := AssociativeArray();
            for d in Keys(V) do
               Vd := V[d];
               VVd := AssociativeArray();
               for r in Keys(Vd) do
                  Vdr := Vd[r];
                  VVd[r] := <Matrix(1, Vdr[1]), Vdr[2]>;
               end for;
               VV[d] := VVd;
            end for;
            V := VV;
 
            function P1rep(x0, check, scaling)
               u0 := x0[1,1] mod I;
               s, u, D1 := Explode(T[u0]);
               v := (s*x0[2,1]) mod I;
               b, t := IsDefined(V[u], v);
               if b then
                  if scaling then
                     return true, t[1], s*t[2];
                  else
                     return true, t[1], _;
                  end if;
               else
                  return false, _, _;
                end if;
            end function;
 
        end if;
 
   end if;

   if debug and Type eq "Matrix" then
      B := ChangeUniverse(Basis(I),O) cat [O| n*Minimum(I) : n in {1..4}];
      S := IsPrime(I) or Minimum(I) eq 1 
           select B else B cat &cat [ChangeUniverse(Basis(P),O) : P in Ps];
      for x in P1 do
         assert Minimum(ideal<O|x[1,1],x[2,1]> + I) eq 1;
         b, xx, s := P1rep(x, true, true);
         assert b and xx eq x;
         assert Minimum(s*O+I) eq 1;
      end for;
      for u,v in Elements(R) do
         b, x, s := P1rep(Matrix(1,[u,v]), true, true);
         if b then
            assert x in P1;
            assert Minimum(s*O+I) eq 1;
            assert (s*u) mod I eq x[1,1] mod I;
            assert (s*v) mod I eq x[2,1] mod I;
         end if;
         u1 := u + Random(B);
         v1 := v + Random(B);
         b1, x1, s1 := P1rep(Matrix(1,[O|u1,v1]), true, true);
         assert b1 eq b;
         if b1 then
            assert x1 eq x;
            assert Minimum(s1*O+I) eq 1;
            assert (s1*u1) mod I eq x1[1,1] mod I;
            assert (s1*v1) mod I eq x1[2,1] mod I;
         end if;
         if Minimum(I) ne 1 then
            s := Random(S);
            assert not P1rep(Matrix(1,[s*u,s*v]), true, true);
         end if;
      end for;
   end if;

   return P1, P1rep, _;
end intrinsic;


// Over Z (for compatibility), interface to Allan's P1

intrinsic ProjectiveLine(R::RngIntRes : Type:="Vector")
       -> SetIndx, UserProgram
{"} // "
   require Type cmpeq "Vector" or Type cmpeq "Matrix": 
     "The optional argument 'Type' should be \"Vector\" or \"Matrix\"";

   N := Modulus(R);
   _P1 := P1Classes(N);

   case Type: when "Vector":

       P1 := _P1; 

       function P1rep(x, check, scaling)
          if check and GCD([N, x[1], x[2]]) ne 1 then
             return false, _, _;
          else
             i, s := P1Reduce(ChangeRing(x,R), _P1);
             return true, P1[i], s;
          end if;
       end function;

   when "Matrix":

       P1 := {@ Transpose(x) : x in _P1 @};

       function P1rep(x, check, scaling)
          if check and GCD([N, x[1,1], x[2,1]]) ne 1 then
             return false, _, _;
          else
             i, s := P1Reduce(Vector(R, Transpose(x)), _P1);
             return true, P1[i], s;
          end if;
       end function;

   end case;

   return P1, P1rep;
end intrinsic;

///////////////////////////////////////////////////////////////////////////
// Orbits under a matrix group action
///////////////////////////////////////////////////////////////////////////

/*
Given a residue ring R = O/I and a sequence 'mats' containing the elements 
of some subgroup of GL(2,R), returns a sequence of integers indicating the 
orbits of ProjectiveLine(R) under the group action

(Too much hassle to establish an intrinsic for this)
*/

function ProjectiveLineOrbits(mats, P1, P1rep)
   if #P1 eq 1 then
      return [1];
   end if;

   orbit_inds := [0 : i in P1];  // indices in range [1 .. number of orbits]
   k := 1; // index of the orbit being computed
   while exists(i){i : i in [1..#P1] | orbit_inds[i] eq 0} do
      orbit_inds[i] := k;
      for M in mats do 
         _, image := P1rep(P1[i]*M, false, false);
         ii := Index(P1, image);  
         error if ii eq 0, 
            "Something is wrong in ProjectiveLineOrbits -- incompatible arguments?";
         orbit_inds[ii] := k;
      end for;
      k +:= 1;
   end while;

   return orbit_inds;
end function;

