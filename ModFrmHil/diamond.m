import !"Geometry/ModFrmHil/definite.m":
  AtkinLehnerDefiniteBig,
  DegeneracyDown1DefiniteBig,
  DegeneracyDownpDefiniteBig,
  HeckeOperatorDefiniteBig;
import !"Geometry/ModFrmHil/hackobj.m" :
  IsBianchi,
  TopAmbient;
import !"Geometry/ModFrmHil/hecke.m" :
  HilbertModularSpaceDirectFactors,
  basis_is_honest,
  basis_matrix,
  debug,
  make_ideal,
  please_report,
  restriction;

import "hackobj.m" : HMF0;
import "hecke_field.m" : hecke_matrix_field, WeightRepresentation;

/**************** New intrinsics **********************/

intrinsic '*'(a::RngOrdIdl, I::AlgAssVOrdIdl) -> AlgAssVOrdIdl
{Given an ideal a of R, and an ideal I of O, an order over R, Returns the ideal a*I.}
  return &+[g * I : g in Generators(a)];
end intrinsic;

/********************************************************/

forward DiamondOperatorDefiniteBig;

// from hecke.m

function operator(M, p, op)
  assert op in {"Hecke", "AL", "DegDown1", "DegDownp", "Diamond"};

  // Check if cached on M
  cached, Tp := IsDefined(eval "M`"*op, p);
  if cached then
    if op eq "Hecke" then
      Tp, p_reps := Explode(Tp);
      return Tp, p_reps;
    else
      return Tp, _;
    end if;
  end if;

  if Dimension(M : UseFormula:=false) eq 0 then // gets cached dimension or computes the space

    Tp := ZeroMatrix(Integers(), 0, 0);

  elif assigned M`basis_matrix_wrt_ambient then

    // (TO DO: is this always better than getting it directly from the big operator?)
    bm := M`basis_matrix_wrt_ambient;
    bmi := M`basis_matrix_wrt_ambient_inv;
    Tp_amb, p_reps := operator(M`Ambient, p, op);
    Tp_amb := ChangeRing(Tp_amb, BaseRing(bm));
    Tp := bm * Tp_amb * bmi;

    if debug and basis_is_honest(M) and Norm(p + Level(M)) eq 1 then
      // check Tp really preserves M as a subspace of M`Ambient
      assert Rowspace(bm * Tp_amb) subset Rowspace(bm);
    end if;

  elif IsBianchi(M) then

    // Always compute and store operator on ambient

    bool, MA := HasAttribute(M, "Ambient");

    if not bool then
      return HeckeMatrixBianchi(M, p);
    end if;

    assert not assigned MA`Ambient;

    Tp := HeckeMatrixBianchi(MA, p);

    bm := M`basis_matrix_wrt_ambient;
    bmi := M`basis_matrix_wrt_ambient_inv;
    return bm * Tp * bmi;

  elif IsDefinite(M) then

    MA := TopAmbient(M);
    case op:
      when "Hecke"   : Tp_big := HeckeOperatorDefiniteBig(MA, p);
      when "AL"      : Tp_big := AtkinLehnerDefiniteBig(MA, p);
      when "DegDown1": Tp_big := DegeneracyDown1DefiniteBig(MA, p);
      when "DegDownp": Tp_big := DegeneracyDownpDefiniteBig(MA, p);
      when "Diamond" : Tp_big := DiamondOperatorDefiniteBig(MA, p);
    end case;
    Tp := restriction(M, Tp_big);
    // TODO abhijitm, this never gets used, it's just to assign something
    p_reps := [1];

  else // indefinite quat order

    disc := make_ideal(Discriminant(QuaternionOrder(M)));
    MA := TopAmbient(M);
    assert disc eq make_ideal(NewLevel(MA));
    N := Level(M)/disc;

    // TODO abhijitm this is to assign variables like M`weight_base_field
    // which might get used later.
    if not assigned M`weight_rep then
      _ := WeightRepresentation(M);
    end if;

    Gamma := FuchsianGroup(QuaternionOrder(M));
    case op:
      when "Hecke" : Tp_big, p_reps := HeckeMatrix2(Gamma, N, p, Weight(M), DirichletCharacter(M));
      when "AL"    : Tp_big := HeckeMatrix2(
                                  Gamma,
                                  N,
                                  p,
                                  Weight(M),
                                  DirichletCharacter(M) : 
                                  UseAtkinLehner);
    end case;
    bm, bmi := basis_matrix(M);
    Tp := restriction(M, Tp_big);

  end if;

  if assigned M`hecke_matrix_field then
    bool, Tp := CanChangeRing(Tp, M`hecke_matrix_field);
    error if not bool,
         "The hecke_matrix_field seems to be wrong!\n" * please_report;
  end if;

  if debug then
    // check commutativity
    bad := Level(M) / NewLevel(M);
    new := Minimum(bad) eq 1;
    for l in Keys(M`Hecke) do
      if new or Minimum(l + bad) eq 1 then
        Tl := M`Hecke[l];
        assert Tl*Tp eq Tp*Tl;
      end if;
    end for;
  end if;

  // Cache
  // (for definite ambient, big matrix is cached instead)
  // TO DO: hecke_algebra etc checks cache directly
  //if not (IsDefinite(M) and not assigned M`Ambient) then
  case op:
    when "Hecke"    : M`Hecke[p]    := <Tp, p_reps>;
    when "AL"       : M`AL[p]       := Tp;
    when "DegDown1" : M`DegDown1[p] := Tp;
    when "DegDownp" : M`DegDownp[p] := Tp;
    when "Diamond"  : M`Diamond[p]  := Tp;
  end case;
  //end if;

  if op eq "Hecke" then
    return Tp, p_reps;
  else
    return Tp, _;
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

function DiamondOperatorDefiniteBig(M, J)
    vprintf HilbertModularForms, 1 :
	"Computing diamond operator for ideal J = %o\n", J;
    assert IsDefinite(M);

    // Form here on we assume this is an ambient space
    assert (not assigned M`Ambient);

    N := Level(M);
    weight2 := Seqset(Weight(M)) eq {2};
    easy := weight2 and N eq Discriminant(QuaternionOrder(M));
    // easy = basis of big space is given by the rids

    if (not assigned M`rids) then
	vprintf HilbertModularForms, 1 :
	    "Right ideal classes were not computed, forcing them to be computed.\n";
	forceSpaceComputation(M);
    end if;

    // !! TODO : This is now redundant, unless the weight is 2
    // Once we get it to work, fix that
    F_weight := getWeightBaseField(M);
    ideal_classes := M`rids;
    h := #ideal_classes;
    vprintf HilbertModularForms, 1 :
	"There are %o O(1)-right ideal classes.\n", h;

    // J acts by left multiplication on the classes of right ideals.
    // This creates a permutation of the ideal classes, which we now construct

    alphas := [];
    perm_inv := [];
    // saving the alphas on the way
    vprintf HilbertModularForms, 1 : "Computing isomorphism between representatives, this might take a while. There are %o...\n", h;
    for rid_idx->I in ideal_classes do
	vprintf HilbertModularForms, 1 :
	    "Working on O(1)-right ideal class representative no. %o.\n", rid_idx;
	t0 := Cputime();
	for j in [1..h] do
	    is_isom, alpha := IsIsomorphic(I, J*ideal_classes[j]);
	    if is_isom then
		Append(~perm_inv, j);
		Append(~alphas, alpha);
		vprintf HilbertModularForms, 1 :
		    "Finding an isomorphism took %o.\n", Cputime() - t0;
		vprintf HilbertModularForms, 1 :
		    "It is isomorphic to J*I[%o].\n", j;
		vprintf HilbertModularForms, 1:
		    "Isomorphism for O(1)-right ideals is given by %o.\n", alpha;
		break;
	    end if;
	end for;
    end for;

    if easy then
	perm := [Index(perm_inv, i) : i in [1..#perm_inv]];
	d_J := PermutationMatrix(F_weight,perm);
	return d_J;
    end if;

    sm := M`splitting_map;
    HMDF := M`ModFrmHilDirFacts;
    nCFD := [#hmdf`CFD : hmdf in HMDF];
    p1reps := [hmdf`PLD`P1Rep : hmdf in HMDF];
    lookups := [hmdf`PLD`Lookuptable : hmdf in HMDF];
    fds := [hmdf`PLD`FD : hmdf in HMDF];
    I := M`rids;
    hh := #I;
    h := &+nCFD;
    F_weight := getWeightBaseField(M);
    wd := M`weight_dimension;
    zero := MatrixAlgebra(F_weight, wd)!0;
    blocks := [[zero : j in [1..h]] : i in [1..h]];
    weight2 := Seqset(Weight(M)) eq {2};
    vprintf HilbertModularForms, 1 :
	"Constructing the big representation matrix...\n";
    for I_src_idx in [1..hh] do
	if (nCFD[I_src_idx] eq 0) then continue; end if;
	vprintf HilbertModularForms, 1 :
	    "Working on O(1)-right ideal class representative no. %o.\n", I_src_idx;
	I_dest_idx := perm_inv[I_src_idx];
	I_src := I[I_src_idx];
	I_dest := I[I_dest_idx];
	alpha_I := alphas[I_src_idx];
	t0 := Cputime();
	for idx->a_src in fds[I_src_idx] do
	    rid_idx := &+nCFD[1..I_src_idx-1];
	    rid_idx +:= idx;
	    _, Ja := p1reps[I_dest_idx](sm(alpha_I)*a_src, true, false);
	    elt_data := lookups[I_dest_idx][Ja];
	    tgt_idx := Index(HMDF[I_dest_idx]`CFD, elt_data[1]);
	    target_idx := &+nCFD[1..I_dest_idx-1];
	    target_idx +:= tgt_idx;
	    u := HMDF[I_dest_idx]`max_order_units[elt_data[2]];

	    if weight2 then
		alpha_rep := IdentityMatrix(F_weight, 1);
	    else
		alpha_rep := M`weight_rep(u^(-1)*alpha_I);
	    end if;
	    blocks[target_idx][rid_idx] := alpha_rep;
	end for;
	vprintf HilbertModularForms, 1 :
	    "Building the row block took %o.\n", Cputime() - t0;
    end for;
    dJ := BlockMatrix(blocks);
    scale := Norm(J)^CentralCharacter(M);
    dJ /:= scale;
    return dJ;
end function;

// This function returns the matrix describing the action
// of the ideal J on the space M of Hilbert modular forms.
// These are the operators denoted by P(J) in [Voight]
// and by S(J) in [Shimura]

intrinsic DiamondOperator(M::ModFrmHil, J::RngOrdIdl) -> AlgMatElt
{Returns the matrix representing the diamond operator <J> on M.}

    // require IsCoprime(J, Level(M)) : "Ideal representative should be coprime to the level";
    // better - we just make it coprime;

    J := CoprimeRepresentative(J, Level(M))*J;
/*
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
    dJ_big := DiamondOperatorDefiniteBig(MA,J);
    return restriction(dJ_big, M);
*/
    return operator(M,J, "Diamond");
end intrinsic;

// Here M is a ModFrmHil (HibertCuspForms(M))
// Currently just works for trivial weight.
function HeckeCharacterSubspace(M, chi)

    K := BaseRing(M);
    Z_K := Integers(K);
    // cl_K, cl_map := RayClassGroup(Level(M), [1..Degree(K)]);
    // This should be enough since the restriction of the character to
    // a Dirichlet character is always trivial, but the above is for debugging
    cl_K, cl_map := ClassGroup(Z_K);
    if IsTrivial(cl_K) then
	return M;
    end if;
    Js := [cl_map(cl_K.i) : i in [1..Ngens(cl_K)]];
    // We make sure these are coprime to the level
    Js := [CoprimeRepresentative(J, Level(M))*J : J in Js];
    dJs := [<J, DiamondOperator(M,J)> : J in Js];

    // checking that the operators commute with the other Hecke operators
    /*
    check_bound := 10;
    hecke := [HeckeOperator(M, PrimeIdealsOverPrime(K,p)[1])
	      : p in PrimesUpTo(check_bound)];
    assert &and[dJ[2]*T eq T*dJ[2] : T in hecke, dJ in dJs];
   */

    F_weight := getWeightBaseField(M);
    Id_M := IdentityMatrix(F_weight, Dimension(M));

    subsp := &meet [Kernel(dJ[2] - chi(dJ[1])*Id_M) : dJ in dJs];

    dim := Dimension(subsp);

    M_sub := HMF0(BaseField(M), Level(M), 1*Integers(K), chi, Weight(M), CentralCharacter(M));
    M_sub`basis_matrix_wrt_ambient := BasisMatrix(subsp);

    L := BaseRing(M_sub`basis_matrix_wrt_ambient);
    Id_Msub := ChangeRing(IdentityMatrix(F_weight, dim),L);

    M_sub`basis_matrix_wrt_ambient_inv :=
        Transpose(Solution( Transpose(M_sub`basis_matrix_wrt_ambient),
			    Id_Msub));
    if assigned M`basis_matrix then
       M_sub`basis_matrix := M_sub`basis_matrix_wrt_ambient *
			     ChangeRing(M`basis_matrix,L);
       M_sub`basis_matrix_inv := Transpose(Solution( Transpose(M_sub`basis_matrix), Id_Msub));
    end if;

    M_sub`Ambient := M;
    M_sub`Dimension := dim;
    if assigned M`is_new then
      M_sub`is_new := M`is_new;
    end if;

    return M_sub;
end function;

// These are only used for debugging purposes
/*
function getEichlerOrder(M, OLI, N)
    // get the Eichler order corresponding to the level N in OLI
    Z_K := BaseRing(OLI);
//    HMDF := M`ModFrmHilDirFacts;
//    N := HMDF[1]`PLD`Level;
    basis_OLI := Generators(OLI);
    sm := M`splitting_map;
    sm_mats := Transpose(Matrix([Eltseq(sm(x)) : x in basis_OLI]));
    rels := Matrix([sm_mats[3]]); // we want upper triangular matrices under sm
    rels := ChangeRing(rels, quo<Z_K | N>);
    ker := Kernel(Transpose(rels));
    ker_basis := [ChangeRing(v, Z_K) : v in Basis(ker)];
    a_invs := [&+[v[i]*basis_OLI[i] : i in [1..#basis_OLI]]
	       : v in ker_basis];
    NOLI := [g*x : g in Generators(N), x in basis_OLI];
    O := Order(a_invs cat NOLI);
    // making sure we obtain a suborder of the right discriminant
    assert Discriminant(O) eq N;
    assert &and[x in OLI : x in Generators(O)];
    return O;
end function;

function getEichlerOrderIdeal(M, OLI, a, O, N)
    Z_K := BaseRing(LeftOrder(OLI));
    // HMDF := M`ModFrmHilDirFacts;
    // N := HMDF[1]`PLD`Level;
    basis_OLI := Generators(OLI);
    sm := M`splitting_map;
    sm_mats := Transpose(Matrix([Eltseq(sm(x)) : x in basis_OLI]));
    // These are matrices that map to a in P1
    rels := Matrix([a[2,1]*sm_mats[1]-a[1,1]*sm_mats[3]]);
    rels := ChangeRing(rels, quo<Z_K | N>);
    ker := Kernel(Transpose(rels));
    ker_basis := [ChangeRing(v, Z_K) : v in Basis(ker)];
    a_invs := [&+[v[i]*basis_OLI[i] : i in [1..#basis_OLI]]
	       : v in ker_basis];
    NOLI := [g*x : g in Generators(N), x in basis_OLI];
    I := rideal< O | a_invs cat NOLI>;
    return I;
end function;
*/
