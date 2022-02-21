import "copypastefunctions.m" : BasisMatrixDefinite,
                                get_tps,
			        IsBianchi,
                                HMF,
                                HMF0,
                                TopAmbient;

/**************** New intrinsics **********************/

intrinsic HilbertCuspForms(
  chi::GrpHeckeElt,
  k::SeqEnum[RngIntElt]
  :
  QuaternionOrder:=0
  ) -> ModFrmHil
{The space of Hilbert modular forms over the totally real number field F,
 with character chi and weight k.
 Here chi should be a Hecke character and k should be a
 sequence of integers.
 If the optional argument QuaternionOrder is specified, this order
 will be used for all computations of the space.}
  N := Modulus(Parent(chi));
  F := NumberField(Order(N));
  require IsAbsoluteField(F) : 
         "The base field F must be an absolute extension of Q";
  require IsTotallyReal(F) : 
         "The base field F must be totally real";
  require #k eq Degree(F) : 
         "The weight k should be a sequence of d integers, where d is the degree of the field";
  require IsArithmeticWeight(F, k) :
         "The weight should be a sequence of integers that are all at least 2, and all of the same parity";
  M := HMF(F, N, k : Chi:= chi, QuaternionOrder:=QuaternionOrder);
  return M;
end intrinsic;

intrinsic '*'(a::RngOrdIdl, I::AlgAssVOrdIdl) -> AlgAssVOrdIdl
{Given an ideal a of R, and an ideal I of O, an order over R, Returns the ideal a*I.}
  return &+[g * I : g in Generators(a)];
end intrinsic;

/********************************************************/

// originally from definite.m
debug := false;

function HeckeOperatorDefiniteBig(M, p : Columns:="all", hack := true)

   assert not assigned M`Ambient; // M is an ambient

   // Caching
   // HeckeBig and HeckeBigColumns must be assigned together

   cached, Tp := IsDefined(M`HeckeBig, p);
   if cached then 
     Tp := Matrix(Tp);
     _, old_cols := IsDefined(M`HeckeBigColumns, p);
     if Columns cmpeq "all" then
       Columns := [1..Ncols(Tp)];
     end if;
     columns := [j : j in Columns | j notin old_cols];
     if IsEmpty(columns) then
       return Tp;
     end if;
   else
     old_cols := [];
     columns := Columns;
   end if;

   A := Algebra(QuaternionOrder(M));
   N := Level(M);
   chi := DirichletCharacter(M);
   weight2 := Seqset(Weight(M)) eq {2};
   easy := weight2 and N eq Discriminant(QuaternionOrder(M));
   // easy = basis of big space is given by the rids

   if not assigned M`basis_matrix then
     _ := BasisMatrixDefinite(M : EisensteinAllowed);
   end if;
   dim := Ncols(M`basis_matrix_big);

   F := M`weight_base_field; // = Q for parallel weight 2
   if easy then
     h := dim;
   else
     HMDF := M`ModFrmHilDirFacts; 
     nCFD := [#xx`CFD : xx in HMDF];
     h := #HMDF;
     wd := M`weight_dimension; // = 1 for weight2
   end if;

   // Columns/columns refer to actual columns of the big matrix, 
   // Bcolumns to columns of large blocks, bcolumns to small blocks

   if columns cmpeq "all" then
     columns := [1..dim];
   else
     columns := Sort([Integers()| i : i in columns]);
   end if;
   assert not IsEmpty(columns) and columns subset [1..dim];

   if not weight2 then // currently, higher weight doesn't use Columns
     columns := [1 .. dim];
   end if;

   if easy then
     bcolumns := columns;
     Bcolumns := columns;
   elif columns eq [1 .. dim] then // full matrix 
     bcolumns := [1 .. dim div wd];
     Bcolumns := [1 .. h];
   elif weight2 then 
     bcolumns := columns;
     Bcolumns := [];
     b := 1;
     for i := 1 to #HMDF do
       e := b + nCFD[i] - 1;
       if exists{x: x in [b..e] | x in columns} then
         Append(~Bcolumns, i);
       end if;
       b := e + 1;
     end for;
   else
     bcolumns := [];
     Bcolumns := [];
     b := 1;
     for i := 1 to #HMDF do
       for j := 1 to nCFD[i] do
         e := b + wd - 1;
         if exists{x: x in [b..e] | x in columns} then
           Append(~bcolumns, e div wd);
           Append(~Bcolumns, i);
         end if;
         b := e + 1;
       end for;
     end for;
   end if;

   if not cached then
     Tp := MatrixRing(F, dim) ! 0; 
   end if;

//"Starting with"; Tp;

//"Columns:"; Columns; old_cols; columns; bcolumns; Bcolumns;

   tp := get_tps(M, p : rows:=Bcolumns); // rows in precompute_tps are columns here

   vprintf ModFrmHil: "%o%o column%o%o of big Hecke matrix (norm %o): ", 
                      #columns eq dim select "All " else "", 
                      #columns, 
                      #columns gt 1 select "s" else "", 
                      #columns gt 1 select "" else " (#"*Sprint(columns[1])*")", 
                      Norm(p);
   vtime ModFrmHil:

   if easy then

      for j in Bcolumns, i in [1..h] do 
         bool, tpji := IsDefined(tp, <j,i>);
         if bool then
            Tp[i,j] := #tpji;
         end if;
      end for;

   else

     sm := M`splitting_map;
     
     checkP1 := Valuation(N,p) gt 0;

     inds := [l : l in [1..#HMDF] | nCFD[l] ne 0];
     row := 0; 
     col := 0;

     for m in inds do 
        if m in Bcolumns then
           for l in inds do 
              bool, tpml := IsDefined(tp, <m,l>);
              if bool then
                 if weight2 then

                    PLDl := HMDF[l]`PLD;
                    FDl   := PLDl`FD; 
                    FDm   := HMDF[m]`PLD`FD; 
                    lookup:= PLDl`Lookuptable; 
                    P1rep := PLDl`P1Rep;

                    Tplm := ExtractBlock(Tp, row+1, col+1, #FDl, #FDm);
                    mms := [mm : mm in [1..#FDm] | col+mm in bcolumns];
                    for ll := 1 to #tpml do
                       mat := tpml[ll] @ sm;
                       for mm in mms do 
                          u := mat * FDm[mm];
                          bool, u0 := P1rep(u, checkP1, false);
                          if bool then
                             n := lookup[u0,1]; 
                             // assert n eq Index(HMDF[l]`CFD, n);
                             // Tplm[n,mm] +:= 1;
			     Tplm[n,mm] +:= chi(Norm(tpml[ll]));
                          end if;
                       end for;
                    end for;
                    InsertBlock(~Tp, Tplm, row+1, col+1);

                 else

                    PLDl  := HMDF[l]`PLD;
                    FDl   := PLDl`FD; 
                    FDm   := HMDF[m]`PLD`FD; 
                    lookup:= PLDl`Lookuptable; 
                    P1rep := PLDl`P1Rep;

                    CFDl := HMDF[l]`CFD; 
                    CFDm := HMDF[m]`CFD; 
                    units1 := HMDF[l]`max_order_units; 
                    weight_map := HMDF[l]`weight_rep; 

                    Tplm := Matrix(F, wd*#CFDl, wd*#CFDm, []);

                    for ll := 1 to #tpml do
                       mat := tpml[ll] @ sm;
                       for mm := 1 to #CFDm do
                          u := mat * FDm[CFDm[mm]];
                          bool, u0 := P1rep(u, checkP1, false);
                          if bool then
                             elt_data := lookup[u0]; 
                             n := Index(CFDl, elt_data[1]);
                             if n ne 0 then
                                quat1 := units1[elt_data[2]]^-1 * tpml[ll]; 
                                X := ExtractBlock(Tplm, (n-1)*wd+1, (mm-1)*wd+1, wd, wd);
                                X +:= chi(Norm(quat1))*weight_map(quat1);
                                InsertBlock(~Tplm, X, (n-1)*wd+1, (mm-1)*wd+1);
                             end if;
                          end if;
                       end for;
                    end for;
                    InsertBlock(~Tp, Tplm, row+1, col+1);

                 end if;
              end if;
              row +:= nCFD[l] * wd;
           end for;
        end if;
        col +:= nCFD[m] * wd;
        row := 0;
     end for;

   end if;

   // new columns were computed, so renew the cache
   M`HeckeBig[p] := SparseMatrix(Tp);
   M`HeckeBigColumns[p] := Sort(old_cols cat columns);
//"Now got columns",  M`HeckeBigColumns[p]; M`HeckeBig[p];

   // Check Hecke invariance of Eisenstein subspace and its complement
   if debug and M`HeckeBigColumns[p] eq [1..dim] then
     if assigned M`InnerProductBig and Norm(p + N) eq 1 
        and p@@cl eq NCl.0 where NCl, cl is NarrowClassGroup(BaseField(M))
     then
       assert Tp * M`InnerProductBig eq M`InnerProductBig * Transpose(Tp);
     end if;
     if assigned M`eisenstein_basis then
       assert Rowspace(M`eisenstein_basis * Tp) subset Rowspace(M`eisenstein_basis);
     end if;
     if assigned M`basis_matrix then
       printf "[debug] Checking space is preserved by Tp: "; time 
       assert Rowspace(M`basis_matrix * Tp) subset Rowspace(M`basis_matrix);
     end if;
   end if;

   return Tp;
end function;

// originally from hecke.m

function hecke_matrix_field(M : hack := true)
  if assigned M`hecke_matrix_field then
    return M`hecke_matrix_field;
  elif IsBianchi(M) or not IsDefinite(M) then
    return Rationals();
  else
      if hack then
	  // hack begins
	  return TopAmbient(M)`weight_base_field;
	  // hack ends
      else
	  return Ambient(M)`weight_base_field;
      end if;
  end if;
end function;

// we compute a Hecke operator to force magma to compute the space
procedure forceSpaceComputation(M)
    K := BaseField(M);
    p := PrimeIdealsOverPrime(K, 2)[1];
    _ := HeckeOperator(M,p);
end procedure;

// a function to find the weight base field of a magma space

function getWeightBaseField(M)
    // is_parallel, w := IsParallelWeight(M);
    if not assigned M`weight_base_field then
	if Seqset(Weight(M)) eq {2} then
	    return Rationals();
	end if;
	if assigned M`basis_matrix_wrt_ambient then
	    return BaseRing(M`basis_matrix_wrt_ambient);
	end if;
	if assigned M`Ambient and assigned M`Ambient`weight_base_field then
	    return M`Ambient`weight_base_field;
	end if;
	forceSpaceComputation(M);
	if assigned M`basis_matrix_wrt_ambient then
	    return BaseRing(M`basis_matrix_wrt_ambient);
	end if;
	if assigned M`Ambient and assigned M`Ambient`weight_base_field then
	    return M`Ambient`weight_base_field;
	end if;
    end if;
    assert assigned M`weight_base_field;
    return M`weight_base_field;
end function;

// TODO : Is this any different than Generators?
function getIdealGens(I)
    return &cat[[g*pb[2] : g in Generators(pb[1])] : pb in PseudoBasis(I)];
end function;

function getEichlerOrder(M)
    // get the Eichler order corresponding to the level of M
    O_B := QuaternionOrder(M);
    Z_K := BaseRing(O_B);
    // N := Level(M);
    HMDF := M`ModFrmHilDirFacts;
    N := HMDF[1]`PLD`Level;
    // basis_O_B := &cat[[g*pb[2] : g in Generators(pb[1])] : pb in PseudoBasis(O_B)];
    basis_O_B := getIdealGens(O_B);
    sm := M`splitting_map;
    sm_mats := Transpose(Matrix([Eltseq(sm(x)) : x in basis_O_B]));
    rels := Matrix([sm_mats[3]]); // we want upper triangular matrices under sm
    rels := ChangeRing(rels, quo<Z_K | N>);
    ker := Kernel(Transpose(rels));
    ker_basis := [ChangeRing(v, Z_K) : v in Basis(ker)];
    a_invs := [&+[v[i]*basis_O_B[i] : i in [1..#basis_O_B]] : v in ker_basis];
    NO_B := [g*x : g in Generators(N), x in basis_O_B];
    O := Order(a_invs cat NO_B);
    assert Discriminant(O) eq Level(M);
    return O;
end function;

// At the moment we assume the action on the rids in trivial level is trivial.
// Later we will change that.
function getActionOnP1Reps(M, J, I_perm)
    sm := M`splitting_map;
    HMDF := M`ModFrmHilDirFacts;
    nCFD := [#hmdf`CFD : hmdf in HMDF];
    p1reps := [hmdf`PLD`P1Rep : hmdf in HMDF];
    lookups := [hmdf`PLD`Lookuptable : hmdf in HMDF];
    O := getEichlerOrder(M);
    // _, alpha := IsPrincipal(rideal<O | Generators(J)>);
    fds := [hmdf`PLD`FD : hmdf in HMDF];
    rid_perms := [];
    I := M`rids;
    for rid_idx in [1..#HMDF] do
	target_idx := I_perm[rid_idx];
	_, alpha := IsIsomorphic(J*I[rid_idx], I[target_idx]);
	rid_perm := [];
	for a in fds[target_idx] do
	    _, Ja := p1reps[target_idx](sm(alpha)*a, true, false);
	    Append(~rid_perm, lookups[target_idx][Ja,1]);
	end for;
	Append(~rid_perms, rid_perm);
    end for;
    cumdims := [&+nCFD[1..i] : i in [0..#nCFD]];
    big_perm := &cat[[cumdims[I_perm[i]] + idx : idx in rid_perms[i]] : i in [1..#rid_perms]];
    assert Set(big_perm) eq {1..&+nCFD};
    return big_perm;
end function;

// originaly from hecke.m
function restriction(T, M : hack := true)
    // needs to force computation of basis_matrix
    if hack and (not assigned M`basis_matrix) then
	forceSpaceComputation(M);
    end if;
    bm := M`basis_matrix;
    bmi := M`basis_matrix_inv;
    bmT := bm * ChangeRing(T, BaseRing(bm));
    if assigned bmi then
	TM := bmT * bmi;
    else
	// solve bm * TM = bmT
	TM, K := Solution(bm, bmT);
	assert Dimension(K) eq 0;
    end if;
    return TM;
end function;

// This function returns the matrix describing the action
// of the ideal J on the space M of Hilbert modular forms.
// These are the operators denoted by P(J) in [Voight]
// and by S(J) in [Shimura]

forward DiamondOperatorBigDefinite;

function DiamondOperator(M, J)
    F_weight := getWeightBaseField(M);
    
    if Dimension(M) eq 0 then
	return MatrixAlgebra(F_weight, 0)!1;
    end if;

    // we compute it on the ambient space
    if assigned M`basis_matrix_wrt_ambient then 

	// (TO DO: is this always better than getting it directly from the big operator?)
	bm := M`basis_matrix_wrt_ambient;
	bmi := M`basis_matrix_wrt_ambient_inv;
	dJ_amb := DiamondOperator(M`Ambient, J);
	dJ_amb := ChangeRing(dJ_amb, BaseRing(bm));
	dJ := bm * dJ_amb * bmi;

	return dJ;
    end if;

    // so far we have implemented it only for the definite spaces
    assert IsDefinite(M);
    MA := TopAmbient(M);
    dJ_big := DiamondOperatorBigDefinite(MA, J);
    return restriction(dJ_big, M);
end function;

function DiamondOperatorBigDefinite(M, J)    

    assert IsDefinite(M);
    
    // Form here on we assume this is an ambient space
    assert (not assigned M`Ambient);
    
    N := Level(M);
    weight2 := Seqset(Weight(M)) eq {2};
    easy := weight2 and N eq Discriminant(QuaternionOrder(M));
    // easy = basis of big space is given by the rids

    // We would have liked to use that, but it is only available for parallel weight 2
    //raw_data := InternalHMFRawDataDefinite(M);
    //ideal_classes := raw_data`RightIdealClassReps;

    //    Instead, we force the computation of the attributes we care about.
    if (not assigned M`rids) then
	forceSpaceComputation(M);
    end if;
    F_weight := getWeightBaseField(M);
    ideal_classes := M`rids;
    h := #ideal_classes;
    
    // J acts by left multiplication on the classes of right ideals.
    JIs := [J*I : I in ideal_classes];
    // This creates a permutation of the ideal classes, which we now construct
    perm := &cat[[j : j in [1..h] | IsIsomorphic(JI, ideal_classes[j])] : JI in JIs];
    
    // TODO - there are more cases to distinguish here.
    // I am not completely sure when and if the direct factors are actually called
    // However, if they are not needed for computing the Hecke operator above,
    // the basis matrix describes the embedding of M into the space of modular forms.
    
    // This is an artifact of the implementation -
    // When the weight is trivial, the basis_matrix describes the cuspidal space inside
    // the entire space of modular forms. We have to dig it out.
    // In the general case, the matrix describes the embedding into the h copies of W.
    // This makes sense since the entire space is cuspidal, but requires different handling.
    
    // if not assigned M`ModFrmHilDirFacts then
    if easy then 
	d_J := PermutationMatrix(F_weight,perm);
//	d_J := Solution(M`basis_matrix, M`basis_matrix * d_J);
	return d_J;
    end if;

    // not easy...
    // In order to gain the action on our space, we have to blockify according to the
    // subspaces of direct factors
    
    HMDF := M`ModFrmHilDirFacts;
    // dimensions of the different H0(W, Gamma_i)
    nCFD := [#xx`CFD : xx in HMDF];
    assert h eq #HMDF;
    wd := M`weight_dimension; // = 1 for weight2

    big_perm := getActionOnP1Reps(M, J, perm);

    // dims := [wd : i in [1..&+nCFD]];
    // cumdims := [&+dims[1..i] : i in [0..#dims]];
    // cumdims := [wd*i : i in [0..&+nCFD]];
    // big_perm := &cat[[cumdims[big_perm[i]]+j : j in [1..dims[i]]] : i in [1..#big_perm]];
    big_perm := &cat[[wd*(big_perm[i]-1)+j : j in [1..wd]] : i in [1..#big_perm]];
    /*
    // cumulative sums for the next line
    cumdims := [&+dims[1..i] : i in [0..#dims]];
    // the blockified permutation
    big_perm := &cat[[cumdims[perm[i]]+j : j in [1..dims[i]]] : i in [1..#perm]];

   */

    // This is the operator on the entire space of Hilbert modular forms
    d_J := PermutationMatrix(F_weight, big_perm);
/*    
    if (M`weight_dimension eq 1) then
	// This is the operator on the subspace corresponding to M
	d_J := Solution(M`basis_matrix, M`basis_matrix * d_J);
    end if;
*/
    return d_J;
end function;

// Here M is a ModFrmHil (HibertCuspForms(M))
// Currently just works for trivial weight.
function HeckeCharacterSubspace(M, chi)
    
    K := BaseRing(M);
    Z_K := Integers(K);
    cl_K, cl_map := RayClassGroup(Level(M), [1..Degree(K)]);
    // This should be enough since the restriction of the character to
    // a Dirichlet character is always trivial, but meanwhile we are on the safe side
    // cl_K, cl_map := NarrowClassGroup(Z_K);
    if IsTrivial(cl_K) then
	return M;
    end if;
    Js := [cl_map(cl_K.i) : i in [1..Ngens(cl_K)]];
    dJs := [<J, DiamondOperator(M,J)> : J in Js];
    
    F_weight := getWeightBaseField(M);
    Id_M := IdentityMatrix(F_weight, Dimension(M));
    
    subsp := &meet [Kernel(dJ[2] - chi(dJ[1])*Id_M) : dJ in dJs];

    dim := Dimension(subsp);
    
    Id_Msub := IdentityMatrix(F_weight, dim);
    
    M_sub := HMF0(BaseField(M), Level(M), 1*Integers(K), chi, Weight(M), CentralCharacter(M));
    M_sub`basis_matrix_wrt_ambient := BasisMatrix(subsp);
    
    M_sub`basis_matrix_wrt_ambient_inv := 
        Transpose(Solution( Transpose(M_sub`basis_matrix_wrt_ambient), Id_Msub));
    if assigned M`basis_matrix then
       M_sub`basis_matrix := M_sub`basis_matrix_wrt_ambient * M`basis_matrix;
       M_sub`basis_matrix_inv := Transpose(Solution( Transpose(M_sub`basis_matrix), Id_Msub));
    end if;

    M_sub`Ambient := M;
    M_sub`Dimension := dim;
    
    return M_sub;
end function;
