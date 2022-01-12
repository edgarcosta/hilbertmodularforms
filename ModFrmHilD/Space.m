/*****
ModFrmHilD
*****/

////////// ModFrmHilD attributes //////////

declare type ModFrmHilD [ModFrmHilDElt];
declare attributes ModFrmHilD:
  Parent, // ModFrmHilDGRng
  Weight, // SeqEnum[RngIntElt]
  Level, // RngOrdIdl
  Basis, // = EisensteinBasis cat CuspFormBasis SeqEnum[ModFrmHilDElt]
  Character, // GrpHeckeElt, JV: why aren't we using Dirichlet?
  EisensteinBasis, // SeqEnum[ModFrmHilDElt]
  CuspFormBasis, // SeqEnum[ModFrmHilDElt]
  EllipticBasis, // SeqEnum[ModFrmHilDElt]
  Dimension, // RngIntElt
  CuspDimension, //RngIntElt
  EisensteinDimension, //RngIntElt
  EisensteinAdmissableCharacterPairs, // List of pairs of primitive characters
  MagmaSpace, //ModFrmHil
  MagmaNewCuspForms; // SeqEnum[ModFrmHilElt]


////////// ModFrmHilD fundamental intrinsics //////////

intrinsic Print(Mk::ModFrmHilD, level::MonStgElt)
  {}
  M := Parent(Mk);
  if level in ["Default", "Minimal", "Maximal"] then
    printf "Space of Hilbert modular forms over %o\n", BaseField(M);
    printf "Precision: %o\n", Precision(M);
    printf "Weight: %o\n", Weight(Mk);
    printf "Character: %o\n", Character(Mk);
    printf "Level: %o", IdealOneLine(Level(Mk));
  elif level eq "Magma" then
    error "not implemented!";
  else
    error "not a valid printing level.";
  end if;
end intrinsic;

intrinsic 'in'(f::., M::ModFrmHilD) -> BoolElt
  {}
  if Type(f) ne ModFrmHilDElt then
    return false, "The first argument should be a ModFrmHilDElt";
  else
    return Parent(f) eq M;
  end if;
end intrinsic;

intrinsic 'eq'(M1::ModFrmHilD, M2::ModFrmHilD) -> BoolElt
  {True iff the two spaces of Hilbert modular forms are identically the same}
return Parent(M1) eq Parent(M2) and Weight(M1) eq Weight(M2) and
Level(M1) eq Level(M2) and Character(M1) eq Character(M2);
end intrinsic;

////////// ModFrmHilD access to attributes //////////

intrinsic Parent(Mk::ModFrmHilD) -> ModFrmHilDGRng
  {}
  return Mk`Parent;
end intrinsic;

intrinsic Weight(Mk::ModFrmHilD) -> SeqEnum[RngIntElt]
  {}
  return Mk`Weight;
end intrinsic;

intrinsic Level(Mk::ModFrmHilD) -> RngOrdIdl
  {}
  return Mk`Level;
end intrinsic;

intrinsic Character(Mk::ModFrmHilD) -> GrpHeckeElt
  {}
  return Mk`Character;
end intrinsic;



/* attributes of the parent */

intrinsic BaseField(Mk::ModFrmHilD) -> Any
  {}
  return BaseField(Parent(Mk));
end intrinsic;

intrinsic Integers(Mk::ModFrmHilD) -> Any
  {}
  return Integers(Parent(Mk));
end intrinsic;

////////// ModFrmHilD creation and multiplication functions //////////

intrinsic ModFrmHilDInitialize() -> ModFrmHilD
  {Create an empty ModFrmHilD object.}
  M := New(ModFrmHilD);
  return M;
end intrinsic;

// TODO: some checks here? or leave it up to the user?
intrinsic HMFSpace(M::ModFrmHilDGRng, N::RngOrdIdl, k::SeqEnum[RngIntElt], chi::GrpHeckeElt) -> ModFrmHilD
  {}
  spaces := Spaces(M);
  if N in Keys(spaces) then
    if <k, chi> in Keys(spaces[N]) then
      return spaces[N][<k, chi>];
    end if;
  end if;
  Mk := ModFrmHilDInitialize();
  Mk`Parent := M;
  Mk`Weight := k;
  Mk`Level := N;
  require Parent(chi) eq HeckeCharacterGroup(N, [1..Degree(BaseField(M))]) : "The parent of chi should be HeckeCharacterGroup(N, [1..Degree(BaseField(M))])";
  comps := Components(chi);
  for i->v in InfinitePlaces(BaseField(M)) do
    chiv := comps[v];
    require chiv(-1) eq (-1)^k[i] : Sprintf("The parity of the character at the infinite place %o doesn not match the parity of the weight", i);
  end for;
  Mk`Character := chi;
  AddToSpaces(M, Mk, N, k, chi);
  return Mk;
end intrinsic;


// overloaded for trivial level and character
intrinsic HMFSpace(M::ModFrmHilDGRng, k::SeqEnum[RngIntElt]) -> ModFrmHilD
  {}
  Mk := ModFrmHilDInitialize();
  Mk`Weight := k;
  ZF := Integers(M);
  N := ideal<ZF|1>;
  X := HeckeCharacterGroup(N, [1..Degree(BaseField(M))]);
  chi := X!1;
  return HMFSpace(M, N, k, chi);
end intrinsic;

// overloaded for trivial character
intrinsic HMFSpace(M::ModFrmHilDGRng, N::RngOrdIdl, k::SeqEnum[RngIntElt]) -> ModFrmHilD
  {}
  Mk := ModFrmHilDInitialize();
  Mk`Weight := k;
  ZF := Integers(M);
  X := HeckeCharacterGroup(N, [1..Degree(BaseField(M))]);
  chi := X!1;
  return HMFSpace(M, N, k, chi);
end intrinsic;

intrinsic ModFrmHilDCopy(Mk::ModFrmHilD) -> ModFrmHilD
  {new instance of ModFrmHilD.}
  M1k := ModFrmHilDInitialize();
  for attr in GetAttributes(Type(Mk)) do
    if assigned Mk``attr then
      M1k``attr := Mk``attr;
    end if;
  end for;
  return M1k;
end intrinsic;


intrinsic NumberOfCusps(Mk::ModFrmHilD) -> RngIntElt
  {Returns the number of cusps for Gamma_0(N)}
  // at the moment Corollary 5.1.27 in the paper
  M := Parent(Mk);
  N := Level(Mk);
  ZF := Integers(M);
  U := UnitGroup(M);
  mU := UnitGroupMap(M);
  hplus := NarrowClassNumber(M);
  h := ClassNumber(ZF);
  // Eran: I'm adding in these lines so that we will
  // quotient out by the totally positive units
  gens := [U.i : i in [1..Ngens(U)]];
  // this matrix is the signature of the generators over Z/2Z
  mat := Matrix([[GF(2)!((1-Sign(x)) div 2) : x in RealEmbeddings(mU(u))]
                 : u in gens]);
  // The kernel recovers the subspace of U/U^2 of totally positive units
  ker := Kernel(mat);
  tot_pos := [&+[b[i]*gens[i] : i in [1..#gens]] : b in Basis(ker)];
  assert &and[IsTotallyPositive(mU(u)) : u in tot_pos];
  U_pos := sub<U | tot_pos cat [2*g : g in gens]>;
  // Helper function
  // This is from corollary 5.1.27 in our paper
  // phi is the size of (Z_F / aa)^{\times} modded out by the totally
  // positive units.
  phi_u := function(aa)
    Q, mQ := quo<ZF | aa>;
    U1,mU1 := UnitGroup(Q);
    // This is wrong, we need to divide only by the totally positive ones
    // S := sub<U1 | [(mQ(mU(e)))@@mU1 : e in Generators(U)]>;
    S := sub<U1 | [(mQ(mU(e)))@@mU1 : e in Generators(U_pos)]>;
    return Integers()!(#U1/#S);
  end function;
  return hplus*h*(&+[phi_u(dd + N/dd) : dd in Divisors(N)]);
end intrinsic;

forward HilbertCharacterSubspace;

intrinsic HilbertCuspForms(Mk::ModFrmHilD) -> ModFrmHil
  {return the Magma's builtin object}
  if not assigned Mk`MagmaSpace then
    require IsTrivial(DirichletRestriction(Character(Mk))): "Magma's builtin tools only supports characters which restrict to trivial Dirichlet characters.";
    Mk`MagmaSpace := HilbertCuspForms(BaseField(Mk), Level(Mk), Weight(Mk));
    Mk`MagmaSpace := HilbertCharacterSubspace(Mk`MagmaSpace, Character(Mk));
  end if;
  return Mk`MagmaSpace;
end intrinsic;

// TODO: could one implement optional parameters without computing a basis
intrinsic Dimension(Mk::ModFrmHilD) -> RngIntElt
  {return the dimension of Mk}
  if not assigned Mk`Dimension then
    Mk`Dimension := EisensteinDimension(Mk) + CuspDimension(Mk);
  end if;
  return Mk`Dimension;
end intrinsic;

intrinsic Dim(Mk::ModFrmHilD) -> RngIntElt
{}
  return Dimension(Mk);
end intrinsic;

// TODO swap the default
intrinsic CuspDimension(Mk::ModFrmHilD : version:="builtin") -> RngIntElt
  {return dimension of S(Mk)}
  require version in ["builtin", "trace"] : "the options for trace are either \"builtin\" or \"trace formula\"";
  if not assigned Mk`CuspDimension then
    k := Weight(Mk);
    if SequenceToSet(k) eq Set([2]) and version eq "trace" then
      print "Juanita: Not using trace formula, might be slow (parallel weight 2). Talk to Ben";
      version := "builtin";
    end if;

    if version eq "builtin" then
      require IsTrivial(Character(Mk)): "we rely on magma built-in functions, which only works for trivial character";
      Mk`CuspDimension := Dimension(HilbertCuspForms(Mk));
    else
      M := Parent(Mk);
      ZF := Integers(M);
      // Edgar: Ben, should one use Strace?
      Mk`CuspDimension := Trace(Mk,1*ZF);
    end if;
  end if;
  return Mk`CuspDimension;
end intrinsic;



intrinsic EisensteinDimension(Mk::ModFrmHilD) -> RngIntElt
  {return the dimension of E(Mk)}
  if not assigned Mk`EisensteinDimension then
    N := Level(Mk);
    newforms_levels := {* Conductor(pair[1]) * Conductor(pair[2]) : pair in EisensteinAdmissableCharacterPairs(Mk) *};
    Mk`EisensteinDimension := &+[Integers()| #Divisors(N/mm)*mult : mm->mult in newforms_levels];
  end if;
  return Mk`EisensteinDimension;
end intrinsic;


intrinsic EisensteinAdmissableCharacterPairs(Mk::ModFrmHilD) -> SeqEnum
  {returns a list of all the primitive pairs <chi1, chi2> such that
  chi1*chi2 = Character(Mk) and Conductor(chi1)*Conductor(chi2) | Leve;(Mk)
  If the weight is 1, we only return pairs up to permutation}
  if not assigned Mk`EisensteinAdmissableCharacterPairs then
    N := Level(Mk);
    k := Weight(Mk);
    if #SequenceToSet(k) ne 1 then
      // there are no Eisenstein series in nonparallel weight
      Mk`EisensteinAdmissableCharacterPairs := [* *];
      return Mk`EisensteinAdmissableCharacterPairs;
    end if;
    k := k[1];
    chi := Character(Mk);
    M := Parent(Mk);
    X := HeckeCharacterGroup(N, [1..Degree(BaseField(M))]);
    assert X eq Parent(chi);
    chis := Elements(X);
    chiscond := [Conductor(c) : c in chis];
    chisdict := AssociativeArray();
    for i->c in chis do
      chisdict[c] := i;
    end for;
    // [i, j] pairs st chis[i]*chis[j] = chi
    pairs := [ [i, chisdict[chi*c^-1]] : i->c in chis ];
    // filter based on conductor
    pairs := [ p : p in pairs | N subset chiscond[p[1]] * chiscond[p[2]] ];
    if k eq 1 then
      // only keep one of the pairs [i, j], [j, i]
      // we E(chi, psi) = E(psi, chi)
      newpairs := [];
      for k0->p in pairs do
        i, j := Explode(p);
        k1 := Index(pairs, [j, i]);
        assert k1 gt 0;
        if k1 ge k0 then
          Append(~newpairs, p);
        end if;
      end for;
      pairs := newpairs;
    end if;
    prims := AssociativeArray();
    for i in SequenceToSet(&cat pairs) do
      prims[i] := AssociatedPrimitiveCharacter(chis[i]);
    end for;
    Mk`EisensteinAdmissableCharacterPairs := [* <prims[p[1]], prims[p[2]]> : p in pairs *];
  end if;
  return Mk`EisensteinAdmissableCharacterPairs;
end intrinsic;

intrinsic '*'(a::RngOrdIdl, I::AlgAssVOrdIdl) -> AlgAssVOrdIdl
{Given an ideal a of R, and an ideal I of O, an order over R, Returns the ideal a*I.}
  return &+[g * I : g in Generators(a)];
end intrinsic;

function getWeightBaseField(M)
    is_parallel, w := IsParallelWeight(M);
    if is_parallel and w eq 2 then
	return Rationals();
    end if;
    assert assigned M`weight_base_field;
    return M`weight_base_field;
end function;

// This function returns the matrix describing the action
// of the ideal J on the space M of Hilbert modular forms.
// These are the operators denoted by P(J) in [Voight]
// and by S(J) in [Shimura]

function DiamondOperator(M, J)

    F_weight := getWeightBaseField(M);
    
    if Dimension(M) eq 0 then
	return MatrixAlgebra(F_weight, 0)!1;
    end if;
    
    // We would have liked to use that, but it is only available for parallel weight 2
    //raw_data := InternalHMFRawDataDefinite(M);
    //ideal_classes := raw_data`RightIdealClassReps;

    //    Instead, we force the computation of the attributes we care about.
    if (not assigned M`rids) then
	K := BaseField(M);
	p := PrimeIdealsOverPrime(K, 2)[1];
	_ := HeckeOperator(M,p);
    end if;
    ideal_classes := M`rids;
    
    // J acts by left multiplication on the classes of right ideals.
    JIs := [J*I : I in ideal_classes];
    // This creates a permutation of the ideal classes, which we now construct
    perm := &cat[[j : j in [1..#ideal_classes] | IsIsomorphic(JI, ideal_classes[j])]
		 : JI in JIs];

    // If the weight is trivial, we do not need the direct factors (and they are aso not computed)
    
    // This is an artifact of the implementation -
    // When the weight is trivial, the basis_matrix describes the cuspidal space inside
    // the entire space of modular forms. We have to dig it out.
    // In the general case, the matrix describes the embedding into the h copies of W.
    // This makes sense since the entire space is cuspidal, but requires different handling.
    if (M`weight_dimension eq 1) then
	d_J := PermutationMatrix(F_weight, perm);
	// This is the operator on the subspace corresponding to M
	d_J := Solution(M`basis_matrix, M`basis_matrix * d_J);
	return d_J;
    end if;

    // case II - nontrivial weight
    
    // In order to gain the action on our space, we have to blockify according to the
    // subspaces of direct factors
    hmsdf := M`ModFrmHilDirFacts;
    // dimensions of the different H0(W, Gamma_i)
    dims := [Nrows(h`basis_matrix) : h in hmsdf];
    // cumulative sums for the next line
    cumsum := [&+dims[1..i] : i in [0..#dims]];
    // the blockified permutation
    big_perm := &cat[[cumsum[perm[i]]+j : j in [1..dims[i]]] : i in [1..#perm]];
    // This is the operator on the entire space of Hilbert modular forms
    d_J := PermutationMatrix(F_weight, big_perm);
    
    return d_J;
end function;

// This function is copied from ModFrmHil/hackobj.m
// Optimally, we would just import it
function HMF0(F, N, Nnew, Chi, k, C)
  M := New(ModFrmHil);
  M`Field := F;
  M`Level := N;
  M`NewLevel := Nnew;
  M`DirichletCharacter := Chi;
  M`Weight := k;
  M`CentralCharacter := C;
  assert C eq Max(k) - 2; // currently
  M`is_cuspidal := true; // always true, currently
  M`Hecke    := AssociativeArray();
  M`HeckeBig := AssociativeArray();
  M`HeckeBigColumns := AssociativeArray();
  M`HeckeCharPoly := AssociativeArray();
  M`AL       := AssociativeArray();
  M`DegDown1 := AssociativeArray();
  M`DegDownp := AssociativeArray();
  if forall{w : w in k | w eq 2} then
    M`hecke_matrix_field := Rationals();
    M`hecke_matrix_field_is_minimal := true;
  else 
    M`hecke_matrix_field_is_minimal := false;
  end if;
  return M;
end function;

// Here M is a ModFrmHil (HibertCuspForms(M))
// Currently just works for trivial weight.
function HeckeCharacterSubspace(M, chi)
    K := BaseRing(M);
    Z_K := Integers(K);
    cl_K, cl_map := NarrowClassGroup(Z_K);
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

// This function test that we have the correct dimension
// for the new subspace of Hilbert modular forms of trivial character
// and weight, for a quadratic field of discriminant d, with level n*Z_K.
// It does so by considering the oriented genera of quaternary
// quadratic forms.
// We restrict to trivial level and weight because
// we don't have access here to the algebraic modular form package
// which can compute those for arbitrary level and weight.
// update : instead of computing on the spot, we just compare to a
// value from a precomputed list.
// This is the computation for d,n - 
// &+[Dimension(OrthogonalModularForms(g[1] : Special))-1
// : g in QuaternaryQuadraticLattices(d*n^2)]
procedure testHeckeCharacterSubspace(d,n)

    // This is the current length of the precomputed list
    assert d*n^2 ne 1 and d*n^2 le 200;
    K := QuadraticField(d);
    D := Discriminant(K);

    // This is currently only worked out for GCD(D,n) eq 1 and n square free
    // (The theorem transferring orthogonal modular forms to Hilbert modular forms)
    assert GCD(D,n) eq 1 and IsSquarefree(n);
    
    dim_list := [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 2, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 3, 2, 0, 0, 3, 2, 0, 0, 4, 2, 0, 0, 0, 2, 0, 0, 1, 3, 0, 0, 1, 2, 0, 0, 4, 3, 0, 0, 0, 0, 0, 0, 7, 4, 0, 0, 5, 3, 0, 0, 5, 4, 0, 0, 5, 3, 0, 0, 0, 4, 0, 0, 6, 8, 0, 0, 0, 4, 0, 0, 4, 4, 0, 0, 8, 1, 0, 0, 10, 3, 0, 0, 7, 0, 0, 0, 0, 6, 0, 0, 4, 5, 0, 0, 8, 5, 0, 0, 10, 7, 0, 0, 0, 8, 0, 0, 11, 6, 0, 0, 9, 2, 0, 0, 12, 6, 0, 0, 10, 9, 0, 0, 4, 10, 0, 0, 14, 0, 0, 0, 10, 7, 0, 0, 8, 11, 0, 0, 4, 7, 0, 0, 11, 8, 0, 0, 11, 0, 0, 0, 0, 9, 0, 0, 0, 8, 0, 0, 2 ];
    
    if Type(K) eq FldRat then
	K := QNF();
    end if;
    Z_K := Integers(K);
    N := ideal<Z_K|n>;

    // We might need that at some point
    // is_new := IsEven(#RealPlaces(K) + #PrimeDivisors(n));
    
    hmf_cusp := NewSubspace(HilbertCuspForms(K, N, 2));
    X := HeckeCharacterGroup(N, [1..#RealPlaces(K)]);
    hmf_triv := HeckeCharacterSubspace(hmf_cusp, X!1);
    dim_hmf_triv := Dimension(hmf_triv);

    
    assert dim_hmf_triv eq dim_list[D*n^2];
    
end procedure;
