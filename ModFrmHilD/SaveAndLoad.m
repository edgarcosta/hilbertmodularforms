///////////////////////////////////////////////////
//                                               //
//    Saving and loading sequences of elements   //
//                                               //
///////////////////////////////////////////////////

intrinsic SaveFilePrefix(Mk::ModFrmHilD) -> MonStgElt
  {
    Builds a prefix encoding the field, level, weight, and character
  }

  // We label number fields by their degree and discriminant
  //
  // TODO abhijitm this is really bad, but it works for me
  // for now. 
  F := BaseField(Mk);
  F_label := Join([IntegerToString(a) : a in DefiningPolyCoeffs(F)], ".");

  // Use the LMFDB label for N
  N := Level(Mk);
  N_label := LMFDBLabel(N);

  k := Weight(Mk);
  // the weight label for [a, b, c, ...] is a.b.c_...
  k_label := Join([IntegerToString(k_i) : k_i in k], ".");

  // If H = HeckeCharacterGroup(N, [1 .. n]),
  // the nebentypus label for H.1^a H.2^b H.3^c ...
  // is a.b.c_...
  //
  // TODO abhijitm this is not canonical and 
  // will become incorrect if Magma changes
  // e.g. how it computes group generators.
  chi := Character(Mk);
  chi_seq := Eltseq(chi);
  chi_label := Join([IntegerToString(chi_cmp) : chi_cmp in chi_seq], ".");

  return Join([F_label, N_label, k_label, chi_label], "-");
end intrinsic;

intrinsic SaveBasis(savefile_name::MonStgElt, B::SeqEnum[ModFrmHilDElt])
  {
    input:
      savefile_name: The file to which we will write
      B: A sequence [f_1, ..., f_n] of ModFrmHilDElts
      savedir: 

    We store the sequence B into the file at savefile_path
    
    Writing f_i^1, ..., f_i^(h+) for the components of f_i,
    each f_i^bb is an ModFrmHilDEltComp with an associated 
    multivariate Puiseux series.

    What we actually store is the 
    SeqEnum[SeqEnum[Tup[RngSerPuisElt, Fld]]]

    [[<f_i^bb`Series, K_i^bb>]_(bb in Cl+)]_(1 <= i <= n),

    where K_i^bb is the coefficient ring of f_i^bb.

    Note that this will OVERWRITE the contents of savedir/savefile_name.
  }
  savefile := Open(savefile_name, "w+");

  if #B eq 0 then
    // some absurdly large value;
    save_prec := 10000;
  else
    save_prec := Min([Precision(f) : f in B]);
    assert &and[save_prec eq Precision(f) : f in B];
  end if;
  WriteObject(savefile, save_prec);

  saveobj := [ElementToCoeffLists(f) : f in B];
  WriteObject(savefile, saveobj);
  // reassigning the variable closes the file
  savefile := 0;
end intrinsic;

intrinsic LoadBasis(loadfile_name::MonStgElt, Mk::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  {
    We recover a basis from a file written to by SaveBasis.
  }
  bbs := NarrowClassGroupReps(Parent(Mk));
  loadfile := Open(loadfile_name, "r");
  saved_prec := ReadObject(loadfile);
  if saved_prec ge Precision(Parent(Mk)) then
    A := ReadObject(loadfile);
    return true, [CoeffListsToElement(Mk, f_coeff_lists) : f_coeff_lists in A];
  else
    return false, _;
  end if;
end intrinsic;

intrinsic ElementToCoeffLists(f::ModFrmHilDElt) -> Tup
  {}
  M := Parent(Parent(f));
  F := BaseField(M);

  coeff_ring_and_prec := <CoefficientRing(f), Precision(f)>;

  // coefficients at the infinity cusps are stored
  // as a list of pairs <bb, coefficient of bb cmp at oo> 
  coeffs_at_infty := [];
  for bb in NarrowClassGroupReps(M) do
    // these are always integral ideals I think
    bb_label := LMFDBLabel(bb);
    a_bb_0 := Coefficient(f, bb, F!0);
    Append(~coeffs_at_infty, <bb_label, a_bb_0>);
  end for;

  // then we iterate through nonzero ideals nn of norm up to Precision(f)
  // and store the sequence of <nn, a_nn>
  coeffs_by_idl := [];
  for nn in IdealsUpTo(Precision(f), F) do
    nn_label := LMFDBLabel(nn);
    Append(~coeffs_by_idl, <nn_label, Coefficient(f, nn)>);
  end for;

  return <coeff_ring_and_prec, coeffs_at_infty, coeffs_by_idl>;
end intrinsic;

intrinsic CoeffListsToElement(Mk::ModFrmHilD, coeff_lists::Tup) -> ModFrmHilDElt
  {}
  M := Parent(Mk);
  F := BaseField(M);
  coeff_ring_and_prec, coeffs_at_infty, coeffs_by_idl := Explode(coeff_lists);
  K, prec := Explode(coeff_ring_and_prec);
  require prec ge Precision(M) : "The loaded coeff_lists have insufficient\
      precision for this space of HMFs";

  // create a power series for each component
  components := AssociativeArray();
  for i->bb in NarrowClassGroupReps(M) do
    bb_label, a_bb_0 := Explode(coeffs_at_infty[i]);
    assert LMFDBLabel(bb) eq bb_label;
    a_bb_0 := StrongCoerce(K, a_bb_0);
    components[bb] := RngSerPuisMonomial(Mk, F!0, a_bb_0);
  end for;

  // iterate through ideals and add monomials 
  // to the appropriate component
  //
  // we populate a dictionary first because
  // IdealsUpTo seems to be nondeterministic when 
  // ordering ideals of the same norm
  coeffs_by_idl_dict := AssociativeArray();
  nonzero_ideals := Exclude(Ideals(M), 0*Integers(F));
  for i in [1 .. #nonzero_ideals] do
    nn_label, a_nn := Explode(coeffs_by_idl[i]);
    coeffs_by_idl_dict[nn_label] := a_nn;
  end for;
    
  for nn in nonzero_ideals do
    a_nn := coeffs_by_idl_dict[LMFDBLabel(nn)];
    bb := IdealToNarrowClassRep(M, nn);
    a_nn := StrongCoerce(K, a_nn);
    components[bb] +:= RngSerPuisMonomial(Mk, nn, a_nn);
  end for;

  // Could contract this into the earlier loop over bbs
  for bb in NarrowClassGroupReps(M) do
    components[bb] := cModFrmHilDEltComp(Mk, bb, components[bb] : 
        coeff_ring := K, prec := Precision(M));
  end for;
       
  return HMFSumComponents(Mk, components);
end intrinsic;


