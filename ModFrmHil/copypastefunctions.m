forward IsBianchi;
forward Ambient;
forward TopAmbient, AtkinLehnerDefiniteBig,
	DegeneracyDownpDefiniteBig;
forward residue_class_reps;
forward get_rids, WeightRepresentation;
forward ComputeBasisMatrixOfNewSubspaceDefinite;
forward RemoveEisenstein;
forward get_tps;
forward RealValuations, junk_for_IsIsomorphic, Jprime,
	ColonInternal, IsIsomorphicInternal, has_element_of_norm;
forward convert_rids, RightIdealClassesAndOrders;
forward get_tps_for_rids, convert_tps;

import "diamond.m" : BasisMatrixDefinite,
                     HeckeOperatorDefiniteBig,
		     HilbertModularSpaceDirectFactors,
		     DegeneracyDown1DefiniteBig;

import "finitefield.m" : reduction_mod_random_large_split_prime;
/********************   from hecke.m    *********************/

debug := false;

please_report :=
"\nPlease send this example to magma-bugs@maths.usyd.edu.au" *
"\n\nHint: to print the entire input of this session, type %P\n";

/* Here we define several record formats. */

ProjectiveLineData:=recformat<FD:SeqEnum,                  // This is a fundamental domain for the the
                                                           // for the action of the unit group on 
							   // in some quaternion algebra on P^1(O/n).

                              Stabs:SeqEnum,               // Generators of the group of stabilizers, for each element in FD.

                              StabOrders:SeqEnum,          // Order of the group of stabilizers, for each element in FD.

                              P1List:SetIndx,              // Elements of the projective line P^1(O/n).

                              P1Rep:UserProgram,           // Function sending [u,v] to an element of P1List.

			      Lookuptable:Assoc,           // Array indexed by P1List with values < FD index, unit index >

			      splitting_map,               // The splitting map mod n for the quaternion order.

             		      Level:RngOrdIdl>;            // The level.
                              

ModFrmHilDirFact:=recformat<PLD,                           // A record with format ProjectiveLineData.

                            CFD:SetIndx,                   // Contributing elements of FD.

                            basis_matrix:Mtrx,             // The rows of this matrix provide a basis for
                                                           // the direct factor of the HMS.

                            basis_matrix_inv:Mtrx,         // basis_matrix*basis_matrix_inv=id.

                            weight_rep:Map,                // The splitting map B -> M_2(K)^g -> GL(V_k) by 
			    				   // which the quaternion algebra acts on the 
							   // weight space V_k.

                            weight_dimension:RngIntElt,    // Dimension of weight space.                
            
                            weight_base_field,             // The base field of the weight representation.

			    max_order_units:SeqEnum>;      // The unit group in the maximal order.


function make_ideal(x)
  case Type(x) :
    when RngIntElt : return x*Integers();
    when FldRatElt : return (Integers()!x)*Integers();
    else           : return x;
  end case;
end function;

// Returns the field currently used as the BaseRing of each HeckeOperator.
// M`hecke_matrix_field is not always assigned; when it is not,
// HeckeOperator returns matrices over the weight_base_field.

function hecke_matrix_field(M)
  if assigned M`hecke_matrix_field then
    return M`hecke_matrix_field;
  elif IsBianchi(M) or not IsDefinite(M) then
    return Rationals();
  else
    return Ambient(M)`weight_base_field;
  end if;
end function;

function basis_is_honest(M)
  return assigned M`basis_is_honest and M`basis_is_honest
         or assigned M`basis_matrix and not assigned M`Ambient;
         // (an ambient is automatically honest)
end function;

// For Fuchsian group Gamma, return a basis matrix for the plus subspace 
// of HeckeMatrix(Gamma, "Infinity") 

function basis_of_plus_subspace(M) 
  Gamma := FuchsianGroup(QuaternionOrder(M));
  N := Level(M) / make_ideal(Discriminant(QuaternionOrder(M)));
  T := HeckeMatrix(Gamma, N, "Infinity");
  if T cmpeq [] then 
    T := Matrix(Integers(), 0, 0, []); 
  end if;
  T := ChangeRing(T, Integers());
  plus_basis := KernelMatrix(T-1);
  plus_basis := ChangeRing(plus_basis, Rationals()); 
  minus_basis := KernelMatrix(T+1);
  minus_basis := ChangeRing(minus_basis, Rationals()); 
  assert Nrows(plus_basis) + Nrows(minus_basis) eq Nrows(T);

  return plus_basis, minus_basis;
end function;

// Given matrices B and C specifying complementary row spaces
// return a matrix Binv satisfying B*Binv = identity, C*Binv = zero

function pseudo_inverse(B, C)
  BC := VerticalJoin(B,C); 
  assert Nrows(BC) eq Ncols(BC);

  verbose := false and IsVerbose("ModFrmHil", 2) and Nrows(BC) ge 500;
  if verbose then
     printf "Finding pseudo-inverse:";
     t0 := Cputime();
  end if;

  I := IdentityMatrix(BaseRing(B), Nrows(B));
  O := ZeroMatrix(BaseRing(C), Nrows(C), Nrows(B));
  IO := VerticalJoin(I,O);
  Binv := Transpose(Solution(Transpose(BC), Transpose(IO)));

  if verbose then
     printf " %o\n", Cputime(t0); 
  end if;

  return Binv;
end function;

// Main function to trigger explicit computation of a space M 

function basis_matrix(M)
  if not assigned M`basis_matrix then

    assert not IsBianchi(M);

    // Determine method for computing M, if not already known
    QO := QuaternionOrder(M);
    ambient := not assigned M`Ambient;

    rel_level := NewLevel(M) / make_ideal(Discriminant(QO));
    assert ambient eq IsOne(rel_level);

    if IsDefinite(M) and ambient then
        _ := BasisMatrixDefinite(M);

    elif IsDefinite(M) and 
         (Seqset(Weight(M)) eq {2} or IsSquarefree(rel_level)) 
    then
        _ := BasisMatrixDefinite(M);

    elif not IsDefinite(M) and ambient then
        plus_basis, minus_basis := basis_of_plus_subspace(M);
        M`basis_matrix := plus_basis;
        M`basis_matrix_inv := pseudo_inverse(plus_basis, minus_basis);
        // TO DO: M`basis_is_honest, right?

    else
        MA := M`Ambient;
        _ := basis_matrix(MA);
        // If MA is honest and we know its inner product, 
        // then we can find an honest basis for M  
        useIP := false;
        if basis_is_honest(MA) then
            try 
                IP := InnerProductMatrix(MA);
                useIP := true;
            catch ERROR
                if "implemented" notin ERROR`Object then 
                    error ERROR`Object;
                end if;
            end try;
        end if;
        vprintf ModFrmHil: 
            "Using naive method to determine new subspace (%ousing inner product)\n", 
             useIP select "" else "not ";
        V := VectorSpace(hecke_matrix_field(MA), Dimension(MA));
        C := sub< V | >;
        if useIP then
            for pp in Factorization(NewLevel(M)/NewLevel(MA)) do
                C +:= NewAndOldSubspacesUsingHeckeAction(MA, pp[1] : OldOnly);
            end for;
            vprintf ModFrmHil, 2: "Computing new space as orthogonal complement of old space: "; 
            vtime ModFrmHil, 2:
            V := Kernel(Transpose(BasisMatrix(C)*IP));
        else
            for pp in Factorization(NewLevel(M)/NewLevel(MA)) do
                new, old := NewAndOldSubspacesUsingHeckeAction(MA, pp[1]);
                V meet:= new;
                C +:= old;
            end for;
        end if;
        R := BaseRing(MA`basis_matrix);
        bm_new := ChangeRing(BasisMatrix(V), R);
        bm_old := ChangeRing(BasisMatrix(C), R);
        M`basis_matrix_wrt_ambient := bm_new;
        M`basis_matrix_wrt_ambient_inv := pseudo_inverse(bm_new, bm_old);
        M`basis_matrix := M`basis_matrix_wrt_ambient * MA`basis_matrix;
        M`basis_matrix_inv := MA`basis_matrix_inv * M`basis_matrix_wrt_ambient_inv;
        M`basis_is_honest := useIP;
/*
 // for testing degeneracy (select the naive method above)
 bm := M`basis_matrix;
 delete M`basis_matrix;
 delete M`basis_matrix_inv;
 delete M`basis_is_honest;
 _ := BasisMatrixDefinite(M);
 assert RowSpace(bm) eq RowSpace(M`basis_matrix);
*/
    end if;

    if assigned M`Dimension then 
      error if M`Dimension ne Rank(M`basis_matrix),
           "\nA serious error has been detected (dimension is wrong!)\n" * please_report;
    else
      M`Dimension := Rank(M`basis_matrix);
    end if;

  end if;

  bool, bmi := HasAttribute(M, "basis_matrix_inv");
  if bool then
    return M`basis_matrix, bmi;
  else
    return M`basis_matrix, _;
  end if;
end function;

function restriction(M, T)
  bm, bmi := basis_matrix(M);
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

////////////////////////////////////////////////////////////////////////////////////////
// Interface for operators (handles caching and calls the appropriate raw function)
////////////////////////////////////////////////////////////////////////////////////////

function checks(M, _p, op)
  p := make_ideal(_p);

  if not (ISA(Type(p), RngOrdIdl) and NumberField(Order(p)) eq BaseField(M)) 
     and not (Type(p) eq RngInt and BaseField(M) eq Rationals()) 
  then
    return false, "The second argument should be an ideal of the base field of the first argument", p;
  end if;

  if IsBianchi(M) then
    if op eq "Hecke" then
      return true, _, p;
    else
      return false, "Not implemented for spaces of Bianchi forms", p;
    end if;
  end if;
    
  if op notin {"Hecke", "AL"} and not IsDefinite(M) then
    return false, "Operator not implemented (for spaces computed with the indefinite algorithm)", p;
  end if;

  if op ne "AL" and not IsPrime(p) then
    return false, "The second argument must be prime", p;
  end if;

  if op ne "Hecke" then
    // must divide the Eichler level
    if not Level(M) subset p * make_ideal(Discriminant(QuaternionOrder(M))) then
      if not Level(M) subset p then
        return false, "The second argument must divide the level of the space", p;
      end if;
      return false, "Operator not implemented in this case (ideal is not coprime to the"
                   *" discriminant of the quaternion order used to compute this space)", p;
    end if;
    if op ne "AL" and Seqset(Weight(M)) ne {2} then
      return false, "Operator is currently implemented only for parallel weight 2", p;
    end if;
  end if;

  return true, _, p;
end function;

function operator(M, p, op)
  assert op in {"Hecke", "AL", "DegDown1", "DegDownp"};

  // Check if cached on M
  cached, Tp := IsDefined(eval "M`"*op, p);
  if cached then 
    return Tp;
  end if;

  if Dimension(M : UseFormula:=false) eq 0 then // gets cached dimension or computes the space

    Tp := ZeroMatrix(Integers(), 0, 0); 

  elif assigned M`basis_matrix_wrt_ambient then 

    // (TO DO: is this always better than getting it directly from the big operator?)
    bm := M`basis_matrix_wrt_ambient;
    bmi := M`basis_matrix_wrt_ambient_inv;
    Tp_amb := operator(M`Ambient, p, op);
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
    end case;
    Tp := restriction(M, Tp_big);

  else // indefinite quat order

    disc := make_ideal(Discriminant(QuaternionOrder(M)));
    MA := TopAmbient(M);
    assert disc eq make_ideal(NewLevel(MA));
    N := Level(M)/disc;

    Gamma := FuchsianGroup(QuaternionOrder(M));
    case op:
      when "Hecke" : Tp_big := HeckeMatrix(Gamma, N, p);
      when "AL"    : Tp_big := HeckeMatrix(Gamma, N, p : UseAtkinLehner);
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
      when "Hecke"    : M`Hecke[p]    := Tp;
      when "AL"       : M`AL[p]       := Tp;
      when "DegDown1" : M`DegDown1[p] := Tp;
      when "DegDownp" : M`DegDownp[p] := Tp;
    end case; 
//end if;

  return Tp;
end function;

intrinsic HeckeOperator(M::ModFrmHil, p::Any) -> Mtrx
{The Hecke operator T_p on the space M of Hilbert modular forms 
 (where p is a prime ideal of the base field of M)}

  bool, err, p := checks(M, p, "Hecke");
  require bool : err;
 
  return operator(M, p, "Hecke");
end intrinsic;

// Returns the field currently used as the BaseRing of each HeckeOperator.
// M`hecke_matrix_field is not always assigned; when it is not,
// HeckeOperator returns matrices over the weight_base_field.

function minimal_hecke_matrix_field(M)
  bool, minimal := HasAttribute(M, "hecke_matrix_field_is_minimal");
  if bool and minimal then
    H := M`hecke_matrix_field;
  elif assigned M`Ambient then
    H := minimal_hecke_matrix_field(M`Ambient);
  elif IsParallelWeight(M) then
    H := Rationals();
  else
    vprintf ModFrmHil: "Figuring out the \'Hecke matrix field\' ... "; 
    time0 := Cputime();

    // The field where they currently live was created as an ext of Kgal.
    // The hecke_matrix_field is the subfield of Kgal corresponding to
    // the subgroup of the Galois group that fixes Weight(M).
    K := BaseField(M);
    assert assigned K`SplittingField; // WeightRepresentation should set it 
    Kgal, rts := Explode(K`SplittingField);
    assert IsAbsoluteField(Kgal);
    Aut, _, Autmap := AutomorphismGroup(Kgal);
    // figure out the Galois group as a permutation group acting on rts
    Sym := SymmetricGroup(AbsoluteDegree(K));
    gens := [Aut.i@Autmap : i in [1..Ngens(Aut)]];
    images := [Sym| [Index(rts, r@a) : r in rts] : a in gens];
    G := sub< Sym | images >;
    Aut_to_G := hom< Aut -> G | images >;
    act := func< w,g | [w[i] : i in Eltseq(g^-1)] >;
    Gw := sub< G | [g : g in G | act(w,g) eq w] > where w is Weight(M);
    Gw_in_Aut := sub< Aut | [h@@Aut_to_G : h in Generators(Gw)] >;
    H := FixedField(Kgal, Gw_in_Aut);  

    vprintf ModFrmHil: "Time: %o\n", Cputime(time0);
  end if;
  return H;
end function;

function random_large_split_prime_using_max_order(K)
  OK := Integers(K);
  while true do
    p := PreviousPrime(Random(B,2*B) : Proof:=false) where B is Round(2^22.5);
    if OK cmpeq Integers() then
      return p;
    elif AbsoluteDiscriminant(OK) mod p eq 0 then
      continue;
    elif exists(P){tup[1] : tup in Factorization(p*OK) | AbsoluteNorm(tup[1]) eq p} then
      assert IsPrime(P);
      return P;
    end if;
  end while;
end function;

function random_large_split_prime(K)
  if Type(K) eq FldRat then
    p := PreviousPrime(Random(B,2*B) : Proof:=false) where B is Round(2^22.5);
    return p;
  end if;
  F := BaseField(K);
  OF := Integers(F);

  assert Ngens(K) eq 1;
  f := DefiningPolynomial(K);
  integral, f := CanChangeRing(f, OF);
  assert integral;
  assert IsMonic(f);
  O := Order(ChangeUniverse(Basis(OF), K) cat [K.1]);

  while true do
    p := random_large_split_prime_using_max_order(F);
    k, res := ResidueClassField(p);
    fp := Polynomial([k| c@res : c in Coefficients(f)]);
    bool, rt := HasRoot(fp);
    if bool and Evaluate(Derivative(fp),rt) ne 0 then
      pbasis := Type(p) eq RngIntElt select [O|p]
                                      else ChangeUniverse(Basis(p),O);
      P := ideal< O | pbasis cat [O| K.1 - (rt@@res)] >;
      assert IsPrime(P);
      return P;
    end if;
  end while;
end function;

// Reduction mod P of a matrix algebra T

function reduction(T, P : res:=0)
  K := BaseRing(T);
  if res cmpne 0 then
    k := Codomain(res);
  elif Type(K) eq FldRat then
    k := GF(P);
    res := map<Rationals() -> k | x :-> k!x>;
  else
    k, res := ResidueClassField(P);
  end if;

/* TO DO: implement CanChangeRing(Mrtx[FldRat], FldFin)
  if Type(K) eq FldRat then
    if ISA(Type(T), Mtrx) then
      return CanChangeRing(T, k);
    else
      U := [];
      for t in GeneratorsSequence(T) do
        bool, u := CanChangeUniverse(t, k);
        if bool then
          Append(~U, u);
        else
          return false, _;
        end if;
        return true, MatrixAlgebra< k, Degree(T) | U >;
      end for;
    end if;
  end if;
*/

  // General case
  // TO DO: implement CanChangeRing(Mtrx, Map)

  function red(t)
    u := MatrixAlgebra(k, Nrows(t)) ! 0;
    flag := true;
    for e in Support(t) do
      i, j := Explode(e);
      try
        u[i,j] := t[i,j] @ res;
      catch E;
        flag := false;
      end try;
    end for;
    if flag then
      return true, u;
    else
      return false, _;
    end if;
  end function;

  if ISA(Type(T), Mtrx) then
    return red(T);
  else
    U := [];
    for t in GeneratorsSequence(T) do
      bool, u := red(t);
      if bool then
        Append(~U, u);
      else
        return false, _;
      end if;
    end for;
    return true, MatrixAlgebra< k, Degree(T) | U >;
  end if;
end function;




// For a matrix algebra U, returns the dimension of the module U*v
// (which is a lower bound on the dimension of U)

function dimension_lower_bound(U : maxdim:=-1, tries:=1, vector:=0, suborbit:=0)
  g := Ngens(U);
  n := Ncols(U.1);
  F := BaseRing(U);
  V := VectorSpace(F, n);
  if maxdim lt 0 then
    maxdim := n; // the strongest lower bound we might obtain
  end if;
  if vector cmpne 0 then
    vectors := [vector];
    assert tries eq 1;
  else
    vectors := [[Random(100) : i in [1..n]] : t in [1..tries]];
    assert suborbit cmpeq 0;
  end if;
  dims := [];
  orbits := [];

  for t := 1 to tries do

    if suborbit cmpne 0 then
      assert g gt 1;
      W := suborbit;
    else
      // First get module generated by images under U.1
      w := V! vectors[t];
      W := sub< V | w >;
      repeat
        w := w*U.1;
        Include(~W, w, ~new);
      until not new;
    end if;
    dim := Dimension(W);

    // Now get the whole module
    if g gt 1 then

// Here the first loop is nicer than the second loop.
// For probabilistic results, use the first loop only.
// Using both seems slightly faster on average than
// using only the second.
if true then
      time0 := Cputime();
      count0 := 10;   // TO DO
      count := count0;
      while dim lt maxdim and count gt 0 do
        i := (suborbit cmpne 0 and Random(1) eq 1)
             select g else Random([1..g]);
        w := Random(Basis(W)) * U.i;
        Include(~W, w, ~new);
        if new then
          count := count0;
        else
          count -:= 1;
        end if;
        dim := Dimension(W);
      end while;
      vprintf ModFrmHil, 2: " [New bit: %o] ", Cputime(time0);
end if;
// dim0 := dim;
if true then
      time0 := Cputime();
      stable := [false : i in [1..g]];
      i := 1;
      while dim lt maxdim and not &and stable do
        i := (i lt g) select i+1 else 1;
        W := Rowspace( VerticalJoin(B, B*U.i) ) where B is BasisMatrix(W);
        if dim eq Dimension(W) then
          stable[i] := true;
        else
          stable := [false : i in [1..g]];
        end if;
        dim := Dimension(W);
      end while;
      vprintf ModFrmHil, 2: " [Old bit: %o] ", Cputime(time0);
end if;
// assert dim0 eq dim;
// if dim0 ne dim then printf "\nFAIL\n[%o, %o]\n", dim0, dim; end if;

    end if;

    Append(~dims, dim);
    Append(~orbits, W);

    if dim eq maxdim then
      break t;
    end if;

  end for; // tries

  _, t := Max(dims);
  return dims[t], vectors[t], orbits[t];
end function;

// The matrix algebra generated by all Hecke operators of a *new* space M.
// The generators are Hecke operators of M, at sufficiently many primes
// (not dividing the level) to generate it.
// Also returns a vector which generates the Hecke module,
// and for later conveniece, the reduction mod P of the matrix algebra.

// TO DO: do not construct any MatrixAlgebra

function hecke_algebra_dimension(M)
  if IsNew(M) then
    d := Dimension(M);
  else
    // TO DO: directly with formula
    F := BaseRing(M);
    k := Weight(M);
    QO := QuaternionOrder(M);
    NN := NewLevel(M);
    vprintf ModFrmHil, 2: "Hecke algebra dimension: ";
    vtime ModFrmHil, 2:
    dims := [ Dimension(NewSubspace(HilbertCuspForms(F, I*NN, k) : QuaternionOrder:=QO))
            : I in Divisors(Level(M)/NN)];
    d := &+ dims;
    if assigned M`include_eis and M`include_eis then
      d +:= NarrowClassNumber(BaseRing(M));
    end if;
    vprintf ModFrmHil, 2: "Hecke algebra dimension: %o = %o (%o)\n", dims, d, Dimension(M);
  end if;
  assert d gt 0;
  return d;
end function;

function hecke_algebra(M : generator:=false, minimal:=true)

  // don't use cached hecke_algebra if basis has since been changed to a rational_basis
  use_cached_hecke_algebra := false;
  if assigned M`hecke_algebra then
    if not assigned M`hecke_matrix_field
      or M`hecke_matrix_field eq BaseRing(M`hecke_algebra[1])
    then
      use_cached_hecke_algebra := true;
    end if;
  end if;

  if not use_cached_hecke_algebra then

    K := BaseRing(M);
    N := Level(M);
    d := Dimension(M);
    da := hecke_algebra_dimension(M);
    assert da gt 0;

    PI := PowerIdeal(Integers(K));
    n := 1;
    if assigned M`UseHardHeckeGenerator then
      n := M`UseHardHeckeGenerator; assert Type(n) eq RngIntElt and n ge 1;
    end if;
    primes_n := [PI|];
    primes_used := [PI|];
    dim := 0;

    vprintf ModFrmHil: "Constructing Hecke algebra of dimension %o:\n", da;
    vtime ModFrmHil:

    i := 0;
    repeat
      dim0 := dim;
      // get another prime pp
      while IsEmpty(primes_n) do
        n +:= 1;
        primes_n := [p: p in PrimesUpTo(n, K : coprime_to:=N) | Norm(p) eq n];
        // sort them in a suitable order (note this is not unique)
        ordering := [<Minimum(p), p> : p in primes_n];
        ParallelSort(~ordering, ~primes_n);
        Reverse(~primes_n);
        if IsBianchi(M) then
          C, mC := ClassGroup(K);
          C2 := 2*C;
          primes_n := [p: p in primes_n | p@@mC in C2];
        end if;
      end while;
      Append(~primes_used, primes_n[#primes_n]);
      Prune(~primes_n);
      heckes := [HeckeOperator(M, p) : p in primes_used];
      F := BaseRing(Universe(heckes));
      T := MatrixAlgebra< F, d | heckes >;
      i +:= 1;
      if i mod 3 eq 1 or Ngens(T) eq 1 then
        U, P := reduction_mod_random_large_split_prime(T, F);
        dim, vec, orbit := dimension_lower_bound(U : maxdim:=da, tries:=1);
      else
        _, U := reduction(T, P); // TO DO: res vararg?
        dim, vec, orbit := dimension_lower_bound(U : maxdim:=da, tries:=1,
                                                 vector:=vec, suborbit:=orbit);
      end if;
      // We very rarely choose a bad random large prime P,
      // but if M decomposes into many pieces, occasionally
      // choose a bad random vector.  (Either way, we then
      // compute unnecessary hecke operators.)
      // The work here (esp for raw spaces) is harder than
      // computing Hecke operators (at least for definite),
      // so take tries = 1, and sometimes reuse P and vec.
assert dim ge dim0; // unless bad P
      if dim le dim0 then
        Prune(~primes_used);
      end if;
    until dim eq da;

if minimal then
    // Second pass, to get a minimal set of generators
    // (this is relatively quick)
    FP := BaseRing(U);
    t := Ngens(T);
    inds := [1..t];
    vprintf ModFrmHil: "Choosing minimal generators for Hecke algebra: \n";
    vtime ModFrmHil:
    for i := 1 to t-1 do
      Ui := MatrixAlgebra< FP, d | [U.j : j in inds | j ne i] >;
      if da eq dimension_lower_bound(Ui : maxdim:=da, vector:=vec) then
        // T.i is redundant
        Exclude(~inds, i);
      end if;
    end for;
    T := MatrixAlgebra< F, d | [T.i : i in inds] >;
    U := MatrixAlgebra< FP, d | [U.i : i in inds] >;
    primes_used := [primes_used[i] : i in inds];
end if;

    assert Ngens(T) gt 0;
    assert Ngens(T) eq #primes_used;
    assert forall{i: i in [1..Ngens(T)] | T.i eq HeckeOperator(M, primes_used[i])};
    if debug then
      assert U eq reduction(T, P);
      assert da eq dimension_lower_bound(U : vector:=vec);
    end if;

    vprintf ModFrmHil: "Hecke algebra is generated by primes of norms %o\n",
                        [Norm(P) : P in primes_used];

    M`hecke_algebra := [* T, primes_used, Vector(F,vec), U, P *];

  end if; // not use_cached_hecke_algebra

  if generator and #M`hecke_algebra eq 5 then

    // Find a single generator of the matrix algebra T,
    // as a combination of the generators T.i
    // Always uses the last generator with coefficient 1

    // Note: testing candidates mod P is quick compared with other things
    // (like finding the min poly of the result), so it's definitely worth
    // looking for a simple combination that works

    d := Dimension(M);
    da := hecke_algebra_dimension(M);
    T, primes_used, vec, TP, P := Explode(M`hecke_algebra);
    vec := Vector(BaseRing(TP), vec);
    g := Ngens(T);

    if g eq 1 then
      M`hecke_algebra cat:= [* T.1, [1] *];

    elif assigned M`UseHardHeckeGenerator then
      // Use combination guaranteed to have distinct eigenvalues
      bounds := [HeckeEigenvalueBound(M, P) : P in primes_used];
      v := [1];
      for i := 2 to g do
        v[i] := Ceiling( v[i-1] * (bounds[i-1] + 1) );
      end for;
      t  := &+ [v[i] * T.i : i in [1..g]];
      tP := &+ [v[i] * TP.i : i in [1..g]];
      assert dimension_lower_bound(MatrixAlgebra<FP,d|tP> : vector:=vec) eq da;

      M`hecke_algebra cat:= [* t, v *];

      vprintf ModFrmHil: "The hard Hecke algebra generator has the form %o * %o\n",
                          v, [Norm(P) : P in primes_used];
    else
      // If hard, use "divide + conquer" strategy
      FP := BaseRing(TP);
      function single_gen(TP, vec : dim:=0)
        if dim eq 0 then
          dim := dimension_lower_bound(TP : vector:=vec);
          // is this necessarily the full dimension of the T associated to TP?
          // (in any case, a rigourous check is done at the end)
          rigour := false;
          dim_known := false;
        else
          dim_known := true;
        end if;
        g := Ngens(TP);
        L := StandardLattice(g-1);
        n := 0;
        count := 0;
        maxcount := 500;
        vprintf ModFrmHil, 2: "(%o)", g;
        while true do
          n +:= 1;
          svs := [tup[1] : tup in ShortVectors(L,n,n) | 0 notin Eltseq(tup[1])];
          for sv in svs, s in {1,-1} do
            count +:= 1;
            vprintf ModFrmHil, 2: ".";
            v := s*sv;
            tP := &+ [v[i]*TP.i : i in [1..g-1]] + TP.g;
            dlb := dimension_lower_bound(MatrixAlgebra<FP,d|tP> : vector:=vec);
            if dlb eq dim then
              return Eltseq(v) cat [1], tP, dim_known;
            elif count ge maxcount and g ge 4 then
              // divide and conquer
              gg := g div 2;
              v1, tP1 := single_gen(MatrixAlgebra<FP,d| [TP.i : i in [1..gg]] >, vec);
              v2, tP2 := single_gen(MatrixAlgebra<FP,d| [TP.i : i in [gg+1..g]] >, vec);
              w, tP := single_gen(MatrixAlgebra<FP,d|tP1,tP2>, vec);
              v := [w[1]*x : x in v1] cat [w[2]*x : x in v2];
              assert tP eq &+ [v[i]*TP.i : i in [1..g]];
              return v, tP, false;
            end if;
          end for; // v
        end while;
      end function;

      vprintf ModFrmHil: "Looking for a single generator of the Hecke algebra: ";
      vprintf ModFrmHil, 2: "\n";
      vtime ModFrmHil:

      v, tP, rigorous := single_gen(TP, vec : dim:=da);
      if not rigorous then
        // Check the result to ensure rigour
        // (dimension_lower_bound may have been used non-rigorously above)
        assert dimension_lower_bound(MatrixAlgebra<FP,d|tP> : vector:=vec) eq da;
      end if;
      assert #v eq g;
      assert tP eq &+ [v[i]*TP.i : i in [1..g]];
      t         := &+ [v[i]*T.i : i in [1..g]];
      M`hecke_algebra cat:= [* t, v *];

      vprintf ModFrmHil: "The Hecke algebra generator has the form %o * %o\n",
                          v, [Norm(P) : P in primes_used];
    end if; // g = 1

  end if; // needed to find generator

  return M`hecke_algebra;
end function;

// assumes poly is monic with coeffs in Z bounded by 'bound'

// TO DO: probably do this for min poly also

function CharacteristicPolynomialViaCRT(T, bound)
  K := BaseRing(T);
  OK := Integers(K);
  error if K eq Rationals(), "Over Q, use internal CharacteristicPolynomial.";

  n := Nrows(T);

  primes := [Integers()| ];
  pols := [* *];

  // use extra primes as a safety check
  extra := 5;
  safety := Ceiling((2^23.5) ^ extra);

  p := Floor(2^23.5);

  while &*primes lt bound*safety do
    p := PreviousPrime(p : Proof:=false);
    if not exists(P){tup[1] : tup in Factorization(p*OK) | Norm(tup[1]) eq p} then
      continue;
    end if;
    vprintf ModFrmHil, 2: ".";
    k, res := ResidueClassField(P);
    TP := Matrix(k, n, [a@res : a in Eltseq(T)]);
    chiP := CharacteristicPolynomial(TP);
    assert IsMonic(chiP);
    if Degree(chiP) eq n then
      Append(~primes, p);
      Append(~pols, chiP);
    end if;
  end while;

  prod := &* primes;
  coeffs := [1 : i in [0..n]];
  for i := 0 to n-1 do
    c := CRT([Integers()!Coefficient(pols[j],i) : j in [1..#primes]], primes);
    // take least residues
    if 2*c gt prod then
      c -:= prod;
    end if;
    coeffs[i+1] := c;
  end for;

  // the following check is likely to fail if answer is bogus and extra > 0
  assert forall{c : c in coeffs | Abs(c) le bound};

  pol := Polynomial(coeffs);

if n le 20 then
 TT := MatrixAlgebra(K, n)! T;
 assert Evaluate(pol, TT) eq 0;
end if;

 return pol;
end function;


function NewformsOfDegree1Implemented(M)
  bool, k := IsParallelWeight(M);
  return bool and k eq 2;
end function;

function basis_is_honest(M)
  return assigned M`basis_is_honest and M`basis_is_honest
         or assigned M`basis_matrix and not assigned M`Ambient;
         // (an ambient is automatically honest)
end function;

// Given matrices B and C specifying complementary row spaces
// return a matrix Binv satisfying B*Binv = identity, C*Binv = zero

function pseudo_inverse(B, C)
  BC := VerticalJoin(B,C);
  assert Nrows(BC) eq Ncols(BC);

  verbose := false and IsVerbose("ModFrmHil", 2) and Nrows(BC) ge 500;
  if verbose then
     printf "Finding pseudo-inverse:";
     t0 := Cputime();
  end if;

  I := IdentityMatrix(BaseRing(B), Nrows(B));
  O := ZeroMatrix(BaseRing(C), Nrows(C), Nrows(B));
  IO := VerticalJoin(I,O);
  Binv := Transpose(Solution(Transpose(BC), Transpose(IO)));

  if verbose then
     printf " %o\n", Cputime(t0);
  end if;

  return Binv;
end function;

// Find an eigenvector of M mod P with eigenvalue e mod P
// Returns false if eigenspace mod P is not dimension 1

function red_eigenvector(M, e, P, res)
//time
//assert not prime_is_in_denom(M, P);
 time
  MP := reduction(M, P : res:=res);
  eP := res(e);
 time
  VP := Eigenspace(MP, eP);
  if Dimension(VP) eq 1 then
    return true, VP.1;
  else
    return false, _;
  end if;
end function;

procedure get_red_vector(EK, tEK, eEK, ~red_vecs : NUM:=1)
  // TO DO ??? will actually want it in the 'raw' basis ???
  Qs := {tup[1] : tup in red_vecs};
  for n := 1 to NUM do
    repeat
      repeat
        vprintf ModFrmHil, 2: "\nChoosing a large split prime: ";
        vtime ModFrmHil, 2:
        Q := random_large_split_prime(EK);
      until Q notin Qs;
      _, res := ResidueClassField(Q);
      okay, vQ := red_eigenvector(tEK, eEK, Q, res);
    until okay;
    Append(~red_vecs, <Q, res, vQ>);
  end for;
end procedure;


/********************   from hackobj.m    *********************/
function IsBianchi(M)
  return ISA(Type(M), ModFrmBianchi);
end function;

function Ambient(M)
  if assigned M`Ambient then
    return M`Ambient;
  else
    // must have decided how to compute M
    assert assigned M`QuaternionOrder or IsBianchi(M);
    return M;
  end if;
end function;

function TopAmbient(M)
  top := M;
  while assigned top`Ambient do
    top := top`Ambient;
  end while;
  return top;
end function;

// create Bianchi space with given ambient
function BMF_with_ambient(A)
  assert not assigned A`Ambient;
  M := New(ModFrmBianchi);
  M`Ambient := A;
  M`Field := A`Field;
  M`Level := A`Level;
  M`DirichletCharacter := 1;
  M`Weight := [2];
  M`CentralCharacter := 0;
  M`is_cuspidal := true; // always true, currently
  M`homology_coefficients := A`homology_coefficients;
  M`ModFrmData := A`ModFrmData;
  M`LevelData := A`LevelData;
  M`Hecke := AssociativeArray();
  M`HeckeCharPoly := AssociativeArray();
  return M;
end function;

// Discriminant of an algebra or order returned as an ideal 
function _Discriminant(A)
  disc := Discriminant(A);
  if Type(disc) eq FldRatElt then disc := Integers()!disc; end if;
  if Type(disc) eq RngIntElt then disc := disc*Integers(); end if;
  return disc;
end function;

procedure set_quaternion_order(M, QO)
   assert not assigned M`QuaternionOrder;
   assert not assigned M`Ambient;
   assert M`Field eq BaseRing(Algebra(QO));
   assert M`NewLevel eq _Discriminant(QO);
   M`QuaternionOrder := QO;

   // cache the space on QO, if caching is switched on
   if assigned M`Field`ModFrmHils then
     if not assigned QO`ModFrmHils then
       QO`ModFrmHils := AssociativeArray();
     end if;
     N := M`Level;
     if IsDefined(QO`ModFrmHils, N) then
       Append(~QO`ModFrmHils[N], M);
assert M in QO`ModFrmHils[N];
     else
       QO`ModFrmHils[N] := [M];
     end if;
   end if;
end procedure;

function is_cached_hmf(QO, F, N, k)
  if QO cmpne 0 and assigned QO`ModFrmHils and IsDefined(QO`ModFrmHils, N) then
    for M in QO`ModFrmHils[N] do
      if Weight(M) eq k then
        return true, M;
      end if;
    end for;
  end if;
  if assigned F`ModFrmHils and IsDefined(F`ModFrmHils, N) then
    Ms := [];
    for M in F`ModFrmHils[N] do 
      if Level(M) eq N and Weight(M) eq k then
        if QO cmpne 0 and assigned M`QuaternionOrder and IsIdentical(M`QuaternionOrder, QO) then
          return true, M;
        elif QO cmpeq 0 then 
          Append(~Ms, M);
        end if;
      end if;
    end for;
    if QO cmpeq 0 then
      if exists(M){M : M in Ms | assigned M`QuaternionOrder} then
        return true, M;
      elif #Ms gt 0 then
        return true, Ms[1];
      end if;
    end if;
  end if;
  return false, _;
end function;

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

function HMF(F, N, k : Chi:=1, QuaternionOrder:=0)

  // TO DO: errors should be passed back to the calling intrinsic

if Chi cmpeq 1 then
  bool, M := is_cached_hmf(QuaternionOrder, F, N, k);
  if bool then
    return M;
  end if;
end if;

  bool, _, _, C := IsArithmeticWeight(F, k); assert bool; // already checked

  M := HMF0(F, N, 1*Integers(F), Chi, k, C);

  if QuaternionOrder cmpne 0 then 
    ok, message := IsSuitableQuaternionOrder(QuaternionOrder, M);
    error if not ok, message;
    set_quaternion_order(M, QuaternionOrder); // cache on QuaternionOrder
  end if;

  // cache on F
  if assigned F`ModFrmHils then
    if IsDefined(F`ModFrmHils, N) then
      Append(~F`ModFrmHils[N], M);
assert M in F`ModFrmHils[N];
    else
      F`ModFrmHils[N] := [* M *];
    end if;
  end if;

  return M;
end function;

/********************   from definite.m    *********************/

function minimal_generators(G)
   gens0 := Generators(G);
   gens := [];
   S := sub<G | >;
   for g in gens0 do 
      if g notin S then
         Append(~gens, g);
         S := sub<G | gens>;
         if S eq G then
            break g;
         end if;
      end if;
   end for;
   return gens;
end function;

function ProjectiveLineOrbits(P1, P1rep, d, unit_map, units, split_map : DoStabs:=true)
   // d is an ideal in the ring of integers of a number field, 
   // P1 is ProjectiveLine(d) which comes with the function P1rep,
   // unit_map is the map returned by UnitGroup for a quaternion order O,
   // units contains its images, in a fixed ordering,
   // split_map is the map to the ResidueMatrixRing(O,d).
   // Returns the orbits of the unit group acting on P1, 
   // and the stabilizers of the first element in each orbit.
  
   OK := Order(d); 
   Rd := quo<OK|d>;
   _, n_seq := residue_class_reps(d);

   U := Domain(unit_map);
   UU := Universe(units);
   assert Type(UU) eq AlgQuat;
   assert units[1] in {UU|1,-1};
   split_units := [u @ split_map : u in units];

   Lookuptable := AssociativeArray(P1);

   if Minimum(d) eq 1 then  // the trivial case
      Lookuptable[P1[1]] := < 1, 1 >;
      PLD := rec< ProjectiveLineData |
                  Level := d,
                  P1List := P1,
                  P1Rep := P1rep,
                  FD := [P1[1]],
                  Lookuptable := Lookuptable,
                  StabOrders := [#units],
                  splitting_map:=split_map 
                >;
      if DoStabs then
         PLD`Stabs := [[ [* UU!(u@unit_map), 1 *]
                       : u in minimal_generators(sub< U | [u@@unit_map : u in units] >)]];
      end if;
      return PLD;
   end if;

   FD := [Universe(P1)| ]; 
   Stabs := [];
   StabOrders := [Integers()| ];

   elts := Set(P1);
 
   vprintf ModFrmHil, 2: "ProjectiveLineOrbits: "; 
   vtime ModFrmHil, 2:

   while not IsEmpty(elts) do 
      e := Rep(elts);
      Append(~FD, e);
      orbit := {};
      stab := [];
      // run through images of e under units,
      // TO DO: skip acting by units[1] = +-1
      for j := 1 to #units do
         e0 := split_units[j] * e;
         _, e1 := P1rep(e0, false, false);
         if e1 notin orbit then
            Exclude(~elts, e1);
            Include(~orbit, e1);
            Lookuptable[e1] := < #FD, j >;
         elif e1 eq e then
            Append(~stab, [* units[j] *]);
         end if;
      end for;

      // assert #units eq (1+#stab) * #orbit;
      Append(~StabOrders, 1+#stab);

      if DoStabs then
         // want stab to contain just generators of the stabilizer
         stab_U := [s[1] @@ unit_map : s in stab];
         stab_U_gens := minimal_generators(sub< U | stab_U >);
         stab_gens := [stab[i] : i in [1..#stab] | stab_U[i] in stab_U_gens];
         Append(~Stabs, stab_gens);
      end if;
   end while;

   vprintf ModFrmHil, 2: "Stabilizers %o\n", Multiset(StabOrders);

   PLD := rec< ProjectiveLineData |
               Level:=d,
               P1List:=P1,
               P1Rep:=P1rep,
               FD:=FD,
               Lookuptable:=Lookuptable,
               StabOrders:=StabOrders,
               splitting_map:=split_map
          >;
   if DoStabs then
      PLD`Stabs:=Stabs;
   end if;
   return PLD;

end function;

function SIntegralPseudoBasis(OH,S) // (OH::AlgAssVOrd, S::SeqEnum) -> SeqEnum
//  Given a maximal order OH and a sequence of prime ideals S, this returns a new pseudo-basis 
//   <I_i, e_i>, i=1,..,4, such that v_p(I_i)>=0 for all p in S. 
   
   error if not forall{p: p in S|IsPrime(p)}, "Elements in the second argument must be primes!";

   OHB:=PseudoBasis(OH); H:=Algebra(OH); O:=Order(OHB[1][1]); NOHB:=[];
   for l:=1 to 4 do
      d:=Denominator(OHB[l][1]);
      T:=[p: p in SequenceToSet([s[1]: s in Factorization(O!!(d*OHB[l][1]))] 
                                                        cat [s[1]: s in Factorization(d*O)] cat S)];
      T:=Sort(T, func<a,b|Norm(a)-Norm(b)>);
      scal:=WeakApproximation(T, [Valuation(OHB[l][1], pr): pr in T]);
      assert (scal in OHB[l][1]); // and (scal*OHB[l][2] in OH);
                                  // This scaling factor must belong to the ideal in the pseudo-basis.
      Append(~NOHB, <scal^-1*OHB[l][1], scal*OHB[l][2]>);
   end for;
   return NOHB;
end function;

function QuotientSplittingData0(OH, OHB, pr, e)
   // Given a maximal order OH, a prime ideal pr and an integer e, this return a sequence of matrices
   // (M_i) in M_2(OK/pr^e) which is a basis of the reduction OH\otimes OK/pr^e\cong M_2(OK/pr^e) as 
   // an (OK/pr^e)-algebra.

   assert IsPrime(pr); 
   assert forall{m: m in [1..4] | Valuation(OHB[m][1], pr) ge 0};

   OK:=Order(pr); R:=quo<OK|pr^e>; 
   embed_mats:=[];
   _, fp2, gp2:=pMatrixRing(OH, pr: Precision:=e+20);
   for m:=1 to 4 do    
      mat_ents:=Eltseq(fp2(OHB[m][2]));
      mat:=Matrix(OK, 2, [OK!(R!(OK!(s@@gp2))): s in mat_ents]);
      Append(~embed_mats, mat);
   end for;

   return embed_mats;
end function;



function QuotientSplittingData(OH, d)
   // Given a maximal order OH and an ideal d, this return a sequence of matrices (M_i) in M_2(OK/d) which 
   // form a basis of the reduction OH\otimes (OK/d)\cong M_2(OK/d) as an (OK/d)-algebra.

   if Minimum(d) eq 1 then
      OHBd:=PseudoBasis(OH); splitting_mats:=[MatrixRing(Order(d), 2)!1: m in [1..4]];
   else 
      OK:=Order(d); div_fact:=Factorization(d); Sd:=[s[1]: s in div_fact];
      div_seq:=[div_fact[m][1]^div_fact[m][2]: m in [1..#div_fact]];
      OHBd:=SIntegralPseudoBasis(OH, Sd);
      embed_mats:=[QuotientSplittingData0(OH, OHBd, div_fact[l][1], div_fact[l][2]): l in [1..#div_fact]];
      splitting_mats:=[];
      for l:=1 to 4 do
         split_mat_ents:=[];
         for m:=1 to 4 do
            elt_red_comp:=[Eltseq(embed_mats[n][l])[m]: n in [1..#div_fact]];
            Append(~split_mat_ents, CRT(elt_red_comp, div_seq));
         end for;
         Append(~splitting_mats, Matrix(OK, 2, split_mat_ents));
      end for;
   end if;
   return OHBd, splitting_mats;
end function;

function _ResidueMatrixRing(OH, d)

   K := NumberField(Order(d));
   OHB, mats := QuotientSplittingData(OH, d); 
   cobi := Matrix(K, [Eltseq(s[2]): s in OHB]) ^ -1;

   return InternalResidueMatrixRingSub(Algebra(OH), d, mats, cobi);
end function;

function InvariantSpace(stab, weight_map, weight_dim, wt_base_field)
   // Given a stabilizer stab (as sequence of quaternions), and a weight representation, 
   // this returns the corresponding invariant space. 

   A:=Domain(weight_map); 
   F:=wt_base_field; 
   V:=VectorSpace(F, weight_dim); 
   V1:=V;
   S := [A| u@Umap : u in Generators(U)] where U, Umap := UnitGroup(BaseField(A));
   S cat:= [s[1] : s in stab | s[1] notin {A|1,-1}]; 
   for s in S do 
      w := weight_map(s);
      V1 meet:= Kernel(w - IdentityMatrix(F, weight_dim));
      if Rank(V1) eq 0 then break; end if;
   end for;

   return BasisMatrix(V1);
end function;

// This is called by HilbertModularSpaceDirectFactors (now only for nontrivial weight)
// P1 = projective line mod d, 
// LO is a quaternion order, 
// split_map LO -> M_2(O/d),
// weight_map = weight_rep

function HMSDF(P1, P1rep, LO, d, split_map, weight_map, weight_dim, wt_base_field)

   U, unit_map:=UnitGroup(LO); 
   units:=[Algebra(LO)! unit_map(s): s in U];
   PLD:=ProjectiveLineOrbits(P1, P1rep, d, unit_map, units, split_map); 
   F:=wt_base_field;
   stabs:=PLD`Stabs; 
   l:=1; 
   repeat 
      M:=InvariantSpace(stabs[l], weight_map, weight_dim, F);
      if Rank(M) eq 0 then l:=l+1; end if;
   until (l gt #stabs) or (Rank(M) ne 0);

   if l gt #stabs then
      return rec<ModFrmHilDirFact|PLD:=PLD, CFD:={@ @}, basis_matrix:=ZeroMatrix(F, 0, 0), 
                 basis_matrix_inv:=ZeroMatrix(F, 0, 0), weight_rep:=weight_map, 
                 weight_dimension:=weight_dim, weight_base_field:=F, max_order_units:=units>;
   else
      contrib_orbs:=[l];
      for m0:=l+1 to #stabs do
         N:=InvariantSpace(stabs[m0], weight_map, weight_dim, F);
         if Rank(N) ne 0 then
            Append(~contrib_orbs, m0);
            nb_rows:=Nrows(M)+Nrows(N); 
            nb_cols:=Ncols(M)+Ncols(N);
            Q:=RMatrixSpace(F, nb_rows, nb_cols)!0; 
            InsertBlock(~Q, M, 1, 1);
            InsertBlock(~Q, N, Nrows(M)+1, Ncols(M)+1); 
            M:=Q;
         end if;
      end for;
      contrib_orbs := {@ x : x in contrib_orbs @}; // SetIndx is better than SeqEnum
   end if;
   N:=Transpose(Solution(Transpose(M), ScalarMatrix(F, Rank(M), 1)));

   return rec<ModFrmHilDirFact|PLD:=PLD, CFD:=contrib_orbs, basis_matrix:=M, basis_matrix_inv:=N, 
   	  		        weight_rep:=weight_map, weight_dimension:=weight_dim, 
                                weight_base_field:=F, max_order_units:=units>;
end function;

function InnerProductMatrixBig(M)
  if not assigned M`InnerProductBig then
    assert not assigned M`Ambient;
    bool, w := IsParallelWeight(M);
    if bool and w eq 2 then
      // Weight 2: inner product is given by the usual mass = 1/#stabilizer
      easy := Level(M) eq Discriminant(QuaternionOrder(M));
      rids := get_rids(M);
      unit_orders := [#UnitGroup(LeftOrder(I)) : I in rids];
      ulcm := LCM(unit_orders);
      if easy then
        masses := [Integers()| ulcm div u : u in unit_orders];
      else
        HMDFs := HilbertModularSpaceDirectFactors(M); assert #HMDFs eq #rids;
        masses := [Integers()| ulcm div x : x in HMDFs[i]`PLD`StabOrders, i in [1..#rids]];
      end if;
      masses := [Integers()| x div g : x in masses] where g is GCD(masses);
      M`InnerProductBig := SparseMatrix(DiagonalMatrix(masses));
    else
      error "Only implemented for weight 2";
    end if;
  end if;
  return Matrix(M`InnerProductBig);
end function;

// Given a vector w of positive integers,
// return a basis matrix B for the orthogonal complement
// (preferably over Z to make Hecke matrices integral)
// and a pseudo inverse Bi

function Zcomplement(w)
  assert Universe(w) eq Integers();
  Q := Rationals();
  n := #w;
  g := GCD(w);
  k := Index(w, g);
  if k eq 0 then
    // TO DO: choose carefully
    g := Min(w);
    k := Index(w, g);
  end if;
  // B  : basis of the kernel of w
  // Bi : pseudo inverse, B*Bi = I
  B := Matrix(Q, n-1, n, []);
  Bi := Matrix(Q, n, n-1, []);
  for i := 1 to k-1 do
    B[i,i] := 1;
    B[i,k] := -w[i]/g;
    Bi[i,i] := 1;
  end for;
  for i := k+1 to n do
    B[i-1,i] := 1;
    B[i-1,k] := -w[i]/g;
    Bi[i,i-1] := 1;
  end for;
  assert IsOne(B * Bi);
  return B, Bi;
end function;

// In parallel weight 2, there are Eisenstein series in the raw space.
// They are easy to write down as "indicator vectors" corresponding 
// to ideal classes.
// TO DO: if CentralCharacter is not 0, can't easily write down the eigenvectors,
// but instead can compute the subspace using that its dimension = h and that it 
// is killed by T_p^e - (Np+1)^e , where e is the exponent of the narrow class group.

function EisensteinBasis(M)
  if assigned M`eisenstein_basis then
    return M`eisenstein_basis;
  end if;

  // M must be an ambient of weight 2
  assert not assigned M`Ambient;
  assert Seqset(Weight(M)) eq {2};

  Cl, Clmap := NarrowClassGroup(BaseField(M));
  // list elts in the same order as the rids
  Clelts := [Cl | cl : cl in Cl]; 
  eltseqs := [Eltseq(cl) : cl in Cl];
  ParallelSort(~eltseqs, ~Clelts); 

  rids := get_rids(M);
  easy := Level(M) eq Discriminant(QuaternionOrder(M));

  if easy then
    // basis is given by rids
    Eis := Matrix(Integers(), #Cl, #rids, []);
    for j := 1 to #rids do 
      cl := Norm(rids[j]) @@ Clmap;
      i := Index(Clelts, cl);
      Eis[i,j] := 1;
    end for;
  else
    b := [Ncols(X`basis_matrix) : X in M`ModFrmHilDirFacts];
    Eis := Matrix(Integers(), #Cl, &+b, []);
    bsum := 0;
    for k := 1 to #b do
      cl := Norm(rids[k]) @@ Clmap;
      i := Index(Clelts, cl);
      for j := bsum + 1 to bsum + b[k] do 
        Eis[i,j] := 1;
      end for;
      bsum +:= b[k];
    end for;
  end if;

  // Check Eis consists of consecutive blocks of ones
  assert Eis eq EchelonForm(Eis);
  assert &+ Eltseq(Eis) eq Ncols(Eis);

  Eis := ChangeRing(Eis, Rationals());
  M`eisenstein_basis := Eis;
  return Eis;
end function;

procedure RemoveEisenstein(~M)
  vprintf ModFrmHil: "Quotienting out the Eisenstein subspace: ";
  time0_eis := Cputime();

  Eis := EisensteinBasis(M);

  IP := InnerProductMatrixBig(M);
  assert IsDiagonal(IP);
  IP := Diagonal(IP);

  Q := Rationals(); // = hecke_matrix_field = weight_base_field
  CEis := Matrix(Q, 0, 0, []);
  BMI := Matrix(Q, 0, 0, []);
  
  b := [&+Eltseq(Eis[i]) : i in [1..Nrows(Eis)]];
  bsum := 0;
  for k := 1 to #b do 
    w := IP[ bsum + 1 .. bsum + b[k] ];
    bsum +:= b[k];
    C, Cinv := Zcomplement(w);
    CEis := DiagonalJoin(CEis, C);
    BMI := DiagonalJoin(BMI, Cinv);
  end for;

  M`basis_matrix := CEis;
  M`basis_matrix_inv := BMI;
  M`basis_is_honest := true;

  if debug then
    dim := Nrows(M`basis_matrix);
    assert Rank(M`basis_matrix) eq dim;
    assert M`basis_matrix * M`basis_matrix_inv eq IdentityMatrix(Q, dim);
  end if;

  vprintf ModFrmHil: "%os\n", Cputime(time0_eis);
end procedure;

function DegeneracyMapDomain(M, d)
   // Given an ambient space M and an integral ideal d such that NewLevel(M) | d | Level(M), 
   // returns a space of level d and same weight as M, defined using internals that are
   // compatible with M (same quaternion algebra, same splitting map and weight representation)

   QO:=M`QuaternionOrder;
   assert NewLevel(M) eq Discriminant(QO);
   assert IsIntegral(d/NewLevel(M));
   assert IsIntegral(Level(M)/d); 

   // MUST use identical internal data: in particular, rids and weight_rep.
   // Call low-level constructor to avoid complications with caching, and don't cache DM
   // TO DO: use cached spaces, to avoid recomputing ModFrmHilDirFacts (that's the only advantage)
   DM:=HMF0(BaseField(M), d, NewLevel(M), DirichletCharacter(M), Weight(M), CentralCharacter(M));
   DM`QuaternionOrder:=QO;
   DM`rids:=get_rids(M);
   DM`splitting_map:=M`splitting_map; // can use same splitting_map even though its level is larger than needed
   DM`weight_base_field:=M`weight_base_field;
   DM`weight_dimension:=M`weight_dimension;
   if Seqset(Weight(M)) ne {2} then // nontrivial weight
      DM`weight_rep:=M`weight_rep; 
   end if;
   return DM;
end function;

// Basis of a newspace (called only by BasisMatrixDefinite)

procedure ComputeBasisMatrixOfNewSubspaceDefinite_general(M)
   assert IsDefinite(M); 
   MA := M`Ambient; // must be assigned with QuaternionOrder (unless NewLevel = Level)
   A,B:= BasisMatrixDefinite(MA);

weight2 := Seqset(Weight(M)) eq {2};
assert not weight2;

   O := Integers(BaseField(M));
   D := Discriminant(QuaternionOrder(M));
   L := Level(M);
   Lnew := NewLevel(M);
   assert NewLevel(MA) eq D; 
   N := Lnew/D; 
   assert ISA(Type(N), RngOrdIdl); // integral
   Nfact := Factorization(N);

   V := VectorSpace(BaseRing(A), Nrows(A)); 
   W := sub<V|>;
   for m := 1 to #Nfact do
      if Dimension(W) eq Dimension(V) then 
         break; 
      end if;

      vprint ModFrmHil: "Computing oldforms relative to prime of norm", Norm(Nfact[m][1]);
      time0 := Cputime();
      IndentPush(); 
      N1 := DegeneracyMapDomain(MA, L/Nfact[m][1]);
      if Dimension(N1) eq 0 then
         IndentPop();
         continue;
      end if;

      P, eP := Explode(Nfact[m]);

      vprintf ModFrmHil: "Degeneracy maps between dimensions %o and %o: ", Dimension(MA), Dimension(N1);
      vtime ModFrmHil:
      D1 := DegeneracyMap(N1, MA, 1*O);

      if eP eq 1 then
         vtime ModFrmHil:
         D2old := DegeneracyMap(N1, MA, P);
      end if;

      if eP gt 1 or debug then
         AL := AtkinLehnerOperator(MA, P);
         D2new := D1 * AL;
      end if;

      D2 := eP eq 1 select D2old else D2new;
      old_space_mat := VerticalJoin(D1, D2);

      // checks
      if eP eq 1 then
         assert Rank(old_space_mat) eq 2*Rank(D1);
         assert Rank(old_space_mat) eq 2*Rank(D2);
         if debug then
            assert RowSpace(old_space_mat) eq RowSpace(D1) + RowSpace(D2new);
         end if;
      end if;

      vprintf ModFrmHil, 2: "Sum of oldspaces: ";
      vtime ModFrmHil, 2:
      W := W + RowSpace(old_space_mat);

      IndentPop(); 
      vprint ModFrmHil: "Time:", Cputime(time0);
      vprint ModFrmHil: "Remaining new space has dimension", Dimension(V) - Dimension(W);
   end for;

   M`basis_is_honest := false;
   M`basis_matrix_wrt_ambient := BasisMatrix(Complement(V, W));
   M`basis_matrix_wrt_ambient_inv := pseudo_inverse(M`basis_matrix_wrt_ambient, BasisMatrix(W));
   M`basis_matrix := M`basis_matrix_wrt_ambient * MA`basis_matrix;
   M`basis_matrix_inv := MA`basis_matrix_inv * M`basis_matrix_wrt_ambient_inv;
end procedure;

procedure ComputeBasisMatrixOfNewSubspaceDefinite(M)
   assert IsDefinite(M); 

   weight2 := Seqset(Weight(M)) eq {2};
   if not weight2 then
      // TO DO implement IP
      ComputeBasisMatrixOfNewSubspaceDefinite_general(M);
      return;
   end if;         

   MA := M`Ambient; // must be assigned with QuaternionOrder (unless NewLevel = Level)
   _ := BasisMatrixDefinite(MA : EisensteinAllowed);
   K := Rationals(); // TO DO: in general MA`weight_base_field;

   F := BaseField(M);
   D := Discriminant(QuaternionOrder(M));
   L := Level(M);
   Lnew := NewLevel(M);
   assert NewLevel(MA) eq D; 
   N := Lnew/D; 
   assert ISA(Type(N), RngOrdIdl); // integral
   assert not IsOne(N);

   vprintf ModFrmHil: "Degeneracy maps for (Eichler) level of norm %o = %o\n",
                       Norm(N), [<Norm(t[1]), t[2]>  : t in Factorization(N)];
   IndentPush();

   eisenstein_present := weight2;
   Ds := <>;
   for t in Factorization(N) do
      P, e := Explode(t);
/*
stuff := DegeneracyUpDefiniteBigStuff(MA, P);
D1new := DegeneracyUp1DefiniteBig(MA, P, stuff);
*/
      // Use upward or downward degeneracy maps? 
      use_up := e eq 1; // for now keep it simple, use up whenever possible

      check := debug and Norm(L) lt 1000 and e eq 1;

      if use_up or check then

         MP := DegeneracyMapDomain(MA, L/P);
         _ := BasisMatrixDefinite(MP : EisensteinAllowed);
         dP := Dimension(MP);
         if dP eq 0 then
            continue t;
         end if;

         vprintf ModFrmHil: "First upward degeneracy operator for prime of norm %o:\n", Norm(P);
         t0 := Cputime();
         IndentPush(); 
         D1 := DegeneracyMap(MP, MA, 1*Integers(F) : Big);
/*
assert    Nrows(D1) eq Nrows(D1new);
assert RowSpace(D1) eq RowSpace(D1new);
*/
         IndentPop(); 
         vprintf ModFrmHil: "%os\n", Cputime(t0);

         vprintf ModFrmHil: "Second upward degeneracy operator for prime of norm %o:\n", Norm(P);
         t0 := Cputime();
         IndentPush(); 
         DP := DegeneracyMap(MP, MA, P : Big);
         IndentPop(); 
         vprintf ModFrmHil: "%os\n", Cputime(t0);
/*
DI := DegeneracyImage(MA, P);
assert RowSpace(DI) eq RowSpace(VerticalJoin(D1,DP)); "okay up";
*/
         IP := ChangeRing(InnerProductMatrixBig(MA), K);
         D1 := Transpose(D1 * IP);
         DP := Transpose(DP * IP);

      end if;
      if not use_up then

         if check then
            D11 := D1;
            DP1 := DP;
            dP1 := dP;
         end if;

         dP := Dimension(NewSubspace(HilbertCuspForms(F, L/P, Weight(M)), D) : UseFormula:=false); 
         if check then
            assert dP eq dP1;
         end if;
         if dP eq 0 then
            continue t;
         end if;

         eisenstein_present := false; // the eisenstein part is not in these kernels

         vprintf ModFrmHil: "First downward degeneracy operator for prime of norm %o:\n", Norm(P);
         t0 := Cputime();
         IndentPush(); 
         D1 := DegeneracyDown1DefiniteBig(MA, P);
         IndentPop(); 
         vprintf ModFrmHil: "%os\n", Cputime(t0);
   
         vprintf ModFrmHil: "Second downward degeneracy operator for prime of norm %o:\n", Norm(P);
         t0 := Cputime();
         IndentPush(); 
         DP := DegeneracyDownpDefiniteBig(MA, P);
         IndentPop(); 
         vprintf ModFrmHil: "%os\n", Cputime(t0);

         // In this situation, delete the precomputation at large primes (or prime powers)
         // (it's too much memory, and the user is not likely to expect it has been done/saved)
         if Norm(P) gt 1000 then
            DeleteHeckePrecomputation(QuaternionOrder(MA), P);
         end if;

         // TO DO: why isn't the sum of the images equal to the P-oldspace?
         if check then
            printf "[debug] Checking that up/down degeneracy agree ... ";
            IP := ChangeRing(InnerProductMatrixBig(MA), K);
            E := Transpose(EisensteinBasis(MA) * IP);
            assert Kernel(HorizontalJoin(D1, DP)) eq Kernel(HorizontalJoin(<D11, DP1, E>));
            /*
            assert Kernel(D1) eq Kernel(HorizontalJoin(D11,E));
            assert Kernel(DP) eq Kernel(HorizontalJoin(DP1,E));
            */
            printf "okay\n";
         end if;

      end if;
/*
IP := ChangeRing(InnerProductMatrixBig(MA), K);
DI := DegeneracyImage(MA, P);
assert Kernel(HorizontalJoin(D1,DP)) eq Kernel(IP*Transpose(DI)); "okay down";
*/
      Append(~Ds, D1);
      Append(~Ds, DP);
   end for;

   if eisenstein_present then
     // the eisenstein part might not have been removed by the kernels
     IP := ChangeRing(InnerProductMatrixBig(MA), K);
     Append(~Ds, Transpose(EisensteinBasis(MA) * IP) );
   end if;

   IndentPop();

   vprintf ModFrmHil: "Kernel of degeneracy maps: ";
   vtime ModFrmHil:
   B := KernelMatrix(HorizontalJoin(Ds));
/*
IP := ChangeRing(InnerProductMatrixBig(MA), K);
for t in Factorization(N) do
 DI := DegeneracyImage(MA, t[1]);
 D1new := DegeneracyUp1DefiniteBig(MA, t[1], 0);
 assert B * IP * Transpose(D1new) eq 0;
 assert B * IP * Transpose(DI) eq 0;
end for;
*/
   vprintf ModFrmHil: "Inverse basis matrix for new space: "; 
   vtime ModFrmHil:
   M`basis_matrix_inv := Transpose(Solution(Transpose(B), MatrixRing(BaseRing(B),Nrows(B))!1));
   M`basis_matrix  := B; 
   M`basis_is_honest := true;
end procedure;

function AtkinLehnerDefiniteBig(M, p)

   assert not assigned M`Ambient; // M is an ambient

   if not assigned M`ALBig then
      M`ALBig := AssociativeArray(Parent(p));
   else
      cached, Wp := IsDefined(M`ALBig, p);
      if cached then
         return Matrix(Wp);
      end if;
   end if;

   N := Level(M) / Discriminant(QuaternionOrder(M));
   e := Valuation(N, p); 
   assert e gt 0;
   pe := p^e;
   NN := N/pe;
   assert ISA(Type(NN), RngOrdIdl); // integral
   ZF := Order(p);
   quope, modpe := quo<ZF|pe>;
   _, P1pe := ProjectiveLine(quope : Type:="Vector");
   // TO DO: if pe = N, use existing P1N

   if not assigned M`basis_matrix then
     _ := BasisMatrixDefinite(M : EisensteinAllowed);
   end if;
   dim := Ncols(M`basis_matrix_big);

   HMDF := M`ModFrmHilDirFacts; 
   nCFD := [#xx`CFD : xx in HMDF];
   h := #HMDF;
   wd := M`weight_dimension; // = 1 for weight2
   F := M`weight_base_field; // = Q for weight2
   sm := M`splitting_map;

   tp := get_tps(M, pe);

   weight2 := Seqset(Weight(M)) eq {2};

   Wp := MatrixRing(F, dim) ! 0; 

   // block[l] = sum of dimensions of blocks [1..l-1]
   block := [0 : l in [1..#HMDF]];
   for l := 1 to #HMDF-1 do
      block[l+1] := block[l] + nCFD[l];
   end for;

   inds := [l : l in [1..#HMDF] | nCFD[l] ne 0];

   for m in inds do 
      ls := {@ l : l in inds | IsDefined(tp, <m,l>) @};

      tp_split_N := AssociativeArray(ls);
      tp_split_pe := AssociativeArray(ls);
      tp_ker := AssociativeArray(ls);
      tp_elt := AssociativeArray(ls); // used when not weight2
      for l in ls do 
         tp_split_N[l]  := {@ @};
         tp_split_pe[l] := {@ @};
         tp_ker[l]      := {@ @};
         tp_elt[l]      := {@ @};
         for t in tp[<m,l>] do
            // this is where we get rid of the extra elements in tps (if e > 1)
            tsN := t@sm;
            tspe := Matrix(2, [x@modpe : x in Eltseq(Transpose(tsN))]);
            bool, tk := P1pe(ChangeRing(Kernel(tspe).1,ZF), true, false);
            if bool then
               Include(~tp_split_N[l],  tsN);
               Include(~tp_split_pe[l], tspe);
               Include(~tp_ker[l],      tk);
               Include(~tp_elt[l],      t);
            end if;
         end for;
         if debug then
            assert forall{t : t in tp_split_pe[l] | Determinant(t) eq 0};
            assert forall{t : t in tp_split_pe[l] | #Kt eq Norm(pe) and Kt subset sub<Kt|Kt.1> where Kt is Kernel(t)};
            assert forall{t : t in tp_split_pe[l] | #It eq Norm(pe) and It subset sub<It|It.1> where It is Image(t)};
            // Kt and It are rank 1 modules; basis in Howell normal form can have 2 elements, but the first generates it
         end if;
      end for;
      if debug and #inds eq #HMDF then
         // The elements tp[<m,?>] are in bijection with P1 under the map t :-> ker(t mod p)
         assert # &join [tp_ker[l] : l in ls] eq (Norm(p)+1)*Norm(p)^(e-1);
      end if;
   
      FDm := HMDF[m]`PLD`FD; 
      for mm in HMDF[m]`CFD do

         // identify the unique t which kills this element in P1 mod p
         _, vpe := P1pe(Eltseq(FDm[mm]), false, false);
         if debug then
            assert #{l : l in ls | vpe in tp_ker[l]} eq 1;
         end if;
         for l_ in ls do
            k := Index(tp_ker[l_], vpe);
            if k ne 0 then
               l := l_;
               break;
            end if;
         end for;

         // get image mod p and then mod N
         imt := Image(tp_split_pe[l,k]);  
         impe := ChangeUniverse(Eltseq(Basis(imt)[1]), ZF);
         if IsOne(NN) then
            imN := impe;
         else
            tv := Eltseq(tp_split_N[l,k] * FDm[mm]);
            imN := [ZF| ChineseRemainderTheorem(pe, NN, impe[i], tv[i]) : i in [1,2]];
         end if;
         // get rep in P1 mod N
         PLDl := HMDF[l]`PLD;
         if debug then
            bool, imN := PLDl`P1Rep(Matrix(1, imN), true, false); assert bool;
         else
            _, imN := PLDl`P1Rep(Matrix(1, imN), false, false);
         end if;

         if weight2 then

            ll := PLDl`Lookuptable[imN, 1];  
            assert ll gt 0;

            r := block[l] + ll;
            c := block[m] + mm;
            assert Wp[r,c] eq 0;
            Wp[r,c] := 1;

         else

            ll, u := Explode(PLDl`Lookuptable[imN]);
            assert ll gt 0;
            rr := Index(HMDF[l]`CFD, ll) - 1;
            cc := Index(HMDF[m]`CFD, mm) - 1;
            assert rr ge 0;
            assert cc ge 0;
            if rr ge 0 then
               r := (block[l] + rr) * wd + 1;
               c := (block[m] + cc) * wd + 1;
               assert IsZero(Submatrix(Wp, r, c, wd, wd));

               units1     := HMDF[l]`max_order_units; 
               weight_map := HMDF[l]`weight_rep; 

               quat1 := units1[u] ^ -1 * tp_elt[l,k];
               InsertBlock(~Wp, weight_map(quat1), r, c);
            end if;

         end if;
           
      end for; // mm
   end for; // m
  
   M`ALBig[p] := SparseMatrix(Wp);
   return Wp;
end function;

// The operator from level N to level N/p 
// given by double cosets of diagonal matrix [1,p]

function DegeneracyDownpDefiniteBig(M, p)

   N := Level(M);
   vp := Valuation(N, p); 
   assert vp gt 0;
 
   D := HeckeOperatorDefiniteBig(M, p);
 
   if vp eq 1 then
      D +:= AtkinLehnerDefiniteBig(M, p);
   end if;
 
   return D;
end function;

// Partition P^1(N) into congruence classes mod N/p
// ie fibres of the map P^1(N) -> P^1(N/p)
// We could do this with P1rep calls in either P^1(N) or P^1(N/p)
// Either way, we would need one P1rep call per element of P^1(N)
// Use P^1(N/p) because the smaller P^1 will sometimes be cheaper

function P1_congruence_classes(P1N, N, Np)

   P1Np, P1repNp := ProjectiveLine(quo<Order(Np)|Np> : Type:="Vector");

   C := [{@ P1N | @} : x in P1Np];
   for v in P1N do
      vNp := Vector([x mod Np : x in Eltseq(v)]);
      _, vNp1 := P1repNp(vNp, false, false);
      i := Index(P1Np, vNp1);
      Include(~C[i], v);
   end for;

   if debug then
      p := N/Np;
      num := Valuation(Np,p) eq 0 select Norm(p)+1 else Norm(p);
      assert forall{c : c in C | #c eq num};
      assert &join C eq P1N;
   end if;

   return C;

end function;

// Tensor product is associative; for efficiency always do
// TensorProduct(small_mat, large_mat)

function weight_map_arch(q, splittings, K, m, n)
   d := #m;
   M := MatrixRing(K,1)!1;
   for l := d to 1 by -1 do
      if m[l] eq 0 and n[l] eq 0 then
         // don't need to modify M
         continue;
      else
         matq := splittings[l](q);
         if n[l] eq 0 then
            M *:= Determinant(matq)^m[l];
         else
            if n[l] eq 1 then
               Ml := matq;
            else
               Ml := SymmetricPower2(matq, n[l]);
            end if;
            if m[l] ne 0 then
               Ml *:= Determinant(matq)^m[l];
            end if;
            if l eq d then
               M := Ml;
            else
               M := TensorProduct(Ml, M);
            end if;
         end if;
      end if;
   end for;
   return M;
end function;

/************************************************************
* from precompute.m
**************************************************************/

// Given a sequence of units in OF that form a subgroup U of OF*/(OF*)^2 
// containing N, the group of norms of OH*, this returns units in OF 
// whose images in OF*/(OF*)^2 form a transversal of U/N 

function units_mod_norms(units, OH)
  OF := BaseRing(OH);
  UF, unitmap := UnitGroup(OF);
  UFmod2, mod2 := quo< UF | 2*UF >;
  norms := {Norm(u) : u in Units(OH)};
  N := sub< UFmod2 | [u @@unitmap @mod2 : u in norms] >;
  U := sub< UFmod2 | [u @@unitmap @mod2 : u in units] >;
  assert N subset U;
  return [t @@mod2 @unitmap : t in Transversal(U,N)];
end function;

function gcd_of_quad_form(M)
  return GCD([M[i,i] : i in [1..Nrows(M)]] cat [2*m : m in Eltseq(M)]);
end function;

// a sequence containing the right ideals in the maximal order O
// that have norm pp, where pp is a prime in the base ring of O
// (there are 1+Norm(pp) such ideals)

function Subideals_of_order(O, pp)
  p := Minimum(pp);
  A := Algebra(O);
  error if not IsMaximal(O), "Error in Subideals: not implemented for non-maximal orders";
  error if not IsPrime(pp), "Error in Subideals: only implemented for prime ideals pp";

  if pp in RamifiedPlaces(A) then
    Isub := ideal<O|pp> + CommutatorIdeal(O);  
    Isub`Norm := pp;
    if IsMaximal(O) then 
      Isub`RightOrder := O; Isub`LeftOrder := O; end if;
    return [Isub]; end if;

  ZbasisO := ZBasis(O);  
  M2F, phi := pMatrixRing(O, pp);
  e11 := Inverse(phi)(M2F.1);
  e21 := Inverse(phi)(M2F.2*M2F.1);
  e11coords, e21coords := Explode(Coordinates( [A!e11,A!e21], ZbasisO ));
  // Reduce mod p otherwise 'rideal' will choke  
  e11red := O! &+[ (e11coords[i] mod p) * ZbasisO[i] : i in [1..#ZbasisO]];
  e21red := O! &+[ (e21coords[i] mod p) * ZbasisO[i] : i in [1..#ZbasisO]];
 
  k, mk := ResidueClassField(Order(pp), pp);
  ideals := [];
  for museq in [[0,1]] cat [[1,x@@mk] : x in k] do
    mu := O!(museq[1]*e11red + museq[2]*e21red);
    I := rideal<O | [mu] cat Generators(pp)>;
    if debug then assert RightOrder(I) eq O; assert Norm(I) eq pp; end if; 
    I`Norm := pp;
    Append( ~ideals, I);
  end for;
  assert #ideals eq Norm(pp)+1;
  return ideals;
end function;

// intersects Subideals_of_order with I, only works for I coprime to pp

function Subideals_of_ideal(I, pp)
  O := Order(I);
  error if not IsRightIdeal(I), "I must be a right ideal";
  if pp in RamifiedPlaces(Algebra(O)) then
    T := Subideals_of_order(O, pp)[1];  assert IsTwoSidedIdeal(T);
    IT := '*'(I, T : Sides:="Right");
    return [ IT ];
  end if;
  error if Norm(GCD(Norm(I), pp)) ne 1, "Norm(I) must be coprime to pp";
  Osubids := Subideals_of_order(O, pp);
  Isubids := [I meet P : P in Osubids];
  Napp := Norm(I)*pp;
  if debug then
    for J in Isubids do 
      assert RightOrder(J) eq O;
      assert Norm(J) eq Napp; end for; 
  end if;
  for i := 1 to #Isubids do Isubids[i]`Norm := Napp; end for;
  return Isubids;
end function;

// Much better way!  It's overkill to use pMatrixRing just to work in I/pp*I.  
// Instead we find elements a*z1+b*z2 in the O-module I/pp*I, which span 2-dim 
// pieces of it.  The subideals are (a*z1+b*z2)*O + pp*I, for (a:b) in P^1(pp).

procedure assign_left_orders(subideals) 
  for I in subideals do if not assigned I`LeftOrder then _ := LeftOrder(I); end if; end for;
end procedure;

function Subideals_of_ideal_newer(I, pp : use_theta:=false)
  vprintf ModFrmHil,2: "_newer: ";
  O := Order(I);  
  OI := LeftOrder(I); 
  A := Algebra(O);
  OF := BaseRing(O);
  error if not IsRightIdeal(I), "I must be a right ideal";
  error if Order(pp) ne OF, "pp must be an ideal of the base order";
  assert IsMaximal(O);

  if pp in RamifiedPlaces(A) then return Subideals_of_ideal(I, pp); end if;

  Fpp, toFpp := ResidueClassField(pp);
  // get a uniformizer with negative valuations at all other places
  ppinv := pp^-1;
  pi := 1/pi1 where _,pi1 := TwoElement(ppinv);  
assert Valuation(pi,pp) eq 1 and 
       &and [tup[2] lt 0 or tup[1] eq pp : tup in Factorization(ideal<OF|pi>)];
   
  // Get bases for O, I and OI for which the coeff ideals are prime to pp, 
  // and for which the basis elements are in O or I
  basisO := Basis(O);  assert Universe(basisO) eq A;
  coeffidlsO := CoefficientIdeals(PseudoMatrix(O));
  for i := 1 to 4 do
    // first arrange that basisO is contained in O
    m := Numerator(Minimum(coeffidlsO[i]));  
    if m ne 1 then  // put 1 in the coeffidl
      coeffidlsO[i] /:= m;
      basisO[i] *:= m;
    end if;
    v := Valuation(coeffidlsO[i], pp); 
    if v ne 0 then
      coeffidlsO[i] /:= pi^v;
      basisO[i] *:= pi^v;
    end if;
  end for;
  assert basisO[1] eq 1; // should be...
  if debug then assert Order(ZBasis(O) cat basisO) eq O; end if;
  
  basisI := Basis(I);  assert Universe(basisI) eq A;
  coeffidlsI := CoefficientIdeals(PseudoMatrix(I));
  for i := 1 to 4 do
    // first arrange that basisI is contained in I
    m := Numerator(Minimum(coeffidlsI[i]));  
    if m ne 1 then  // put 1 in the coeffidl
      coeffidlsI[i] /:= m;
      basisI[i] *:= m;
    end if;
    v := Valuation(coeffidlsI[i], pp); 
    if v ne 0 then
      assert v lt 0;
      coeffidlsI[i] /:= pi^v;
      basisI[i] *:= pi^v;
    end if;
  end for;
  if debug then assert rideal<O| ZBasis(I) cat basisI> eq I; end if;

  basisOI := Basis(OI);  assert Universe(basisOI) eq A;
  coeffidlsOI := CoefficientIdeals(PseudoMatrix(OI));
  for i := 1 to 4 do
    // first arrange that basisOI is contained in OI
    m := Numerator(Minimum(coeffidlsOI[i]));  
    if m ne 1 then  // put 1 in the coeffidl
      coeffidlsOI[i] /:= m;
      basisOI[i] *:= m;
    end if;
    v := Valuation(coeffidlsOI[i], pp); 
    if v ne 0 then
      coeffidlsOI[i] /:= pi^v;
      basisOI[i] *:= pi^v;
    end if;
  end for;
  assert basisOI[1] eq 1; // should be...
  if debug then assert Order(ZBasis(OI) cat basisOI) eq OI; end if;
/*
myOI := Order(A, PseudoMatrix( coeffidlsOI, Matrix([Eltseq(A!basisOI[i]) : i in [1..4]]) ) );
//assert myOI cmpeq OI;
assert &and [zb in myOI : zb in ZBasis(OI)] and &and [zb in OI : zb in ZBasis(myOI)];
*/
  // Write down the module action of O/pp*O on I/pp*I, as matrices over Fpp 
  // for basisO[2] and basisO[3] (since these generate the ring O/pp*O).
  // Note that O multiplies I from the right.   We express the action 
  // in terms of 4x4 row matrices (so these also act on the right).
  action_mats := [];
  basisI_mat := Matrix([ Eltseq(c) : c in basisI ]);
  basisI_mat_inv := basisI_mat ^-1;
  for b in basisO[2..3] do 
    coords_wrt_A := Matrix([ Eltseq(c*b) : c in basisI ]);
    coords_wrt_basisI := coords_wrt_A * basisI_mat_inv;
    mat := Matrix(Fpp,4,4, [cc@toFpp : cc in Flat(Eltseq(coords_wrt_basisI))] );
                            // there are no pp's in the denoms
    Append(~action_mats, mat);
  end for;

  // The ideals we want correspond to the 2-dim O-submodules of I/pp*I. 
  // We find a 2-dim subspace S (not an O-submodule), such that each element
  // of S generates a 2-dim O-submodule (yielding 1+#Fpp distinct ones in total).
  // Under a splitting I/pp*I == Mat(2,Fpp), S would have the shape [* 0 // * 0], 
  // and the submodules would be [a 0 // b 0]*Mat(2,Fpp) for (a:b) in P^1(Fpp).
  // We obtain S as the image of M-gamma*I, where gamma is an eigenvalue in Fpp of M.
  // The elements of O satisfy quadratic polynomials, hence the (nonscalar) matrices  
  // in the Fpp-span of the two action_mats will have quadratic min polys, and it's
  // not hard to show this must split into linear factors for some M in the span.  
  for s in Fpp do 
    M := action_mats[1] + s*action_mats[2];
    minpol := MinimalPolynomial(M);  assert Degree(minpol) eq 2;
    f := Factorization(minpol)[1][1];
    if Degree(f) gt 1 then continue; end if;
    fM := Evaluate(f, M);
    S := RowSpace(fM); // = image of fM
    break;
  end for;
  error if not assigned fM, 
       "Failed to find a matrix (in the 2-dim span) with an eigenvalue in Fpp";
  z1 := &+[ (S.1)[i]@@toFpp * basisI[i] : i in [1..4]]; 
  z2 := &+[ (S.2)[i]@@toFpp * basisI[i] : i in [1..4]]; 

  // The subideals are (a*z1+b*z2)*O + pp*I, as (a:b) runs through P^1(Fpp)
  ppI := HermiteForm(PseudoMatrix( [pp*CI : CI in coeffidlsI], Matrix([Coordinates(O,c) : c in basisI]) ));
  ppNI := pp*Norm(I); // = the norm of all the subidls
  subideals := [];
  P1Fpp := [ [Fpp|1,0] ] cat [ [x,1] : x in Fpp ];
  for ab in P1Fpp do 
    a,b := Explode(ab);  //"a =", a, "b =", b;
    gen_mod_pp := a*S.1 + b*S.2;  assert not IsZero(gen_mod_pp);
    gen := a@@toFpp * z1 + b@@toFpp * z2;
    // figure out 2 elements of basisO to span the image of (a*z1+b*z2)*O in I/pp*I
    inds := [1];  // since gen*1 is not in pp*I
    for i := 2 to 4 do 
      // if basisO[2,3] don't work, then basisO[4] must
      if i eq 4 or Rank(VerticalJoin( gen_mod_pp, gen_mod_pp*action_mats[i-1] )) eq 2 then
        Append(~inds,i); break; end if;
    end for;
    genO := PseudoMatrix( coeffidlsO[inds], Matrix([Coordinates(O,gen*basisO[i]) : i in inds]) );
    Isub := rideal<O| HermiteForm(VerticalJoin(ppI, genO)) : Check:=debug>; 
    if debug then assert RightOrder(Isub) eq O; assert Norm(Isub) eq ppNI; assert Isub subset I; 
    else Isub`RightOrder := O; Isub`Norm := ppNI; end if;
    Append(~subideals, Isub);
  end for;
  if debug then assert &and [subideals[i] ne subideals[j] : j in [1..i-1], i in [1..#subideals]]; end if;

  if use_theta then
    vprintf ModFrmHil, 2: "Left orders of subideals "; vtime ModFrmHil, 2:
    assign_left_orders(subideals);  
  end if;

  return subideals;
  
  /********    Compute the left orders of the subideals    ********/
  
  // Identify OI/pp with Mat(2,Fpp) via the action of OI/pp on the 2-dimensional module S
  left_action_mats := [IdentityMatrix(Fpp,2)]; // because basisOI[1] = 1
  assert basisOI[1] eq 1;
  for b in basisOI[2..4] do 
    cols := [];
    for z in [z1,z2] do 
      coords_wrt_basisI := Vector(Eltseq(b*z)) * basisI_mat_inv;
      coords_wrt_S := Coordinates(S, S![cc@toFpp : cc in Eltseq(coords_wrt_basisI)] );
                          // there are no pp's in the denoms
      Append(~cols, coords_wrt_S);
    end for;
    Append(~left_action_mats, Transpose(Matrix(cols)) );
  end for;

  // Choose elements of OI that reduce mod pp to the standard basis elements of Mat(2,Fpp)
  cob := Matrix(Fpp,4,4, [Eltseq(mat) : mat in left_action_mats] );
  bool, cob_inv := IsInvertible(cob);  assert bool;
  m11,m12,m21,m22 := Explode([A| &+[ r[i]@@toFpp * basisOI[i] : i in [1..4] ] : r in Rows(cob_inv) ]);

basisOI_mat := Matrix([ Eltseq(c) : c in basisOI ]);
for i := 1 to 4 do mm := [m11,m12,m21,m22][i];
 assert Vector( [c@toFpp : c in Eltseq(mm_A*basisOI_mat^-1) where mm_A := Vector(Eltseq(A!mm))] ) * cob 
     eq Vector( [Fpp| i eq j select 1 else 0 : j in [1..4]] ); end for; 

  // Write down the left order for each (a:b).  
  // Note that the subideal is locally principal, and modulo pp it is generated by 
  // the matrix [a r*p // b s*p] for any r,s for which a*s-b*r is nonzero mod pp.
  // To get the left order we conjugate OI by this matrix and add pp*OI.
  ppOI := HermiteForm(PseudoMatrix( [pp*CI : CI in coeffidlsOI], Matrix([Eltseq(c) : c in basisOI]) ));
  _,pi := TwoElement(pp); // the standard uniformiser
  one := ideal<OF|1>;
  left_orders := [];
time
  for i := 1 to #P1Fpp do 
    Isub := subideals[i];
    ppIsub := rideal<O| PseudoMatrix( [pp*CI : CI in CoefficientIdeals(pm)], Matrix(pm) ) 
                       : Check:=false> where pm is PseudoMatrix(Isub);
    ZBIsub := ZBasis(Isub); // TO DO: don't do this, of course
    a,b := Explode(P1Fpp[i]);  
    if b eq 0 then  
      // take [r,s] = [0,1]
      elts := [A| m11, m22];  xx0 := m12;  
 xx1 := m21;
    else assert b eq 1;  
      // take [r,s] = [1,0]
      aa := a@@toFpp;
      elts := [A| m11+m22, m11-aa*m12];  xx0 := aa*(m11-m22)-aa^2*m12+m21;  
 xx1 := (a eq 0) select m12 else m21;
    end if;
    // We know there's an element xx in pp*LeftOrder(Isub) with xx == xx0 mod pp; we now lift it mod pp^2
    // TO DO ... rewrite efficiently + get it right...
    flag := false;
    ppxx1 := pi*xx1;
    for s in Fpp do 
      xx := xx0 + s@@toFpp * ppxx1;
      if &and [xx*zb in ppIsub : zb in ZBIsub] then flag := true; break s; end if;
    end for;  assert flag; 
 /* ppm12 := pi*m12;  ppm21 := pi*m21;  
    flag := false;
    Fpp_classes := [ s@@toFpp : s in Fpp ];
    for s1 in Fpp_classes do for s2 in Fpp_classes do  
      xx := xx0 + s1*ppm12 + s2*ppm21; 
      // check if xx*Isub is contained in pp*Isub
      if &and [xx*zb in ppIsub : zb in ZBIsub] then flag := true; break s1; end if;
    end for; end for;  assert flag; 
 */
    conj := PseudoMatrix( [one,one,ppinv], Matrix([Eltseq(X) : X in elts cat [xx]]) ); // coords in terms of Basis(A)
    left_order := Order(A, HermiteForm(VerticalJoin(conj, ppOI)) );
    Append(~left_orders, left_order);
  end for;

printf "debug (check LeftOrder):  "; time
  for i in [1..#subideals] do 
if true or debug then 
      LOi := LeftOrder(subideals[i]);
      assert LOi eq left_orders[i]; 
      /*
      assert &and [b1*b2 in LOi : b1,b2 in ZBasis(LOi)]; // check they are really rings
      assert &and [b1*b2 in left_orders[i] : b1,b2 in ZBasis(left_orders[i])]; 
      assert IsMaximal(LOi) and IsMaximal(left_orders[i]);
      assert &and [zb in LOi : zb in ZBasis(left_orders[i])] and 
             &and [zb in left_orders[i] : zb in ZBasis(LOi)]; 
      */
    else subideals[i]`LeftOrder := left_orders[i]; end if;
  end for;
  return subideals;
end function;

// Let I1, .., Ih denote the ridls.  For a prime power P = PP^eP,
// tps[<j,i>] := sequence of reps t in A, up to units of LeftOrder(Ii)
// such that P*Ii < t*Ij < Ii and the size of (t*Ij)\Ii is Norm(P)^2
// (Note that when eP > 1, we don't remove the "non-Hecke elements" here)

forward TotallyPositiveUnits;

procedure precompute_tps(OH, P, ridls, record_idx, rows)

  H := Algebra(OH);
  F := BaseField(H);  
  OF := Integers(F);
  
  Pfact := Factorization(P);
  assert #Pfact eq 1; // must be prime power
  PP, eP := Explode(Pfact[1]);
  NP := Norm(P);
  NPP := Norm(PP);
  ramified := P in RamifiedPlaces(H);
  assert eP eq 1 or not ramified;
  if ramified then
    num := 1;
  elif eP eq 1 then
    num := NP + 1;
  else
    NPP := Norm(PP);
    num := (NPP^(eP+1) - 1) div (NPP - 1);
  end if;

  h := #ridls;
  assert rows subset [1..h];

  // TO DO: distinct left orders may be isometric, when Disc(H) ne 1
  // (it's unavoidable if we insist on strict_support in get_rids).
  // It just means redundant work computing thetas, norm_one_units etc
  ords := [];
  order_indices := [];
  for I in ridls do 
    for i := 1 to #ords do
      if IsIdentical(ords[i], I`LeftOrder) then 
        Append(~order_indices, i); 
        continue I; 
      end if;
    end for;
    Append(~ords, I`LeftOrder);
    Append(~order_indices, #ords); 
  end for;

  vprintf ModFrmHil: "Precomputation" * (debug select " (in debug mode): " else ": ") * "\n";
  IndentPush();
  time0 := Cputime();
  vprint ModFrmHil, 3: "Left order classes of the right ideal classes are", order_indices;

  pos_units := TotallyPositiveUnits(OF);
  for l := 1 to #ords do 
    LO := ords[l];
    if not assigned LO`norm_one_units_mod_scalars then
      n1group, n1map := NormOneGroup(LO : ModScalars);
      LO`norm_one_units_mod_scalars := [u@n1map : u in n1group];
    end if;
    if not assigned LO`pos_scalar_units_mod_norms then
      LO`pos_scalar_units_mod_norms := units_mod_norms(pos_units, LO);
    end if;
  end for;
  pos_units_mod_norms := [LeftOrder(I)`pos_scalar_units_mod_norms : I in ridls];
  real_places := RealPlaces(F);
  U, Umap := IndependentUnits(OF);
  Uvals := [RealValuations(RealPlaces(F), Umap(U.i)) : i in [1..Ngens(U)]]; 
  UnitRealValuations := <U, Umap, Uvals>;

  // Decide whether to use small prime method for the prime P, 
  // and whether it's worth using thetas
  // TO DO: rethink this -- if the colons etc are known, the large prime method is very quick,
  //        at least until the field degree gets too large.  A nice example is Q(sqrt(82)).
  C := #NarrowClassGroup(F); // known
  use_theta := h gt 10 and #ords gt 1  // could be worthwhile 
               and rows eq [1..h];     // TO DO for arbitrary rows(?)
  small_prime := eP eq 1; // subideals code assumes P is prime
  small_prime and:= ramified or
    use_theta select 10*num le #rows/C // would be 1*num if thetas distinguished all orders, and ignoring all overhead
               else h/2*num le #rows/C;
  use_theta and:= small_prime; // only the small_prime method involves thetas

  if not assigned OH`RightIdealClasses[record_idx]`rids_narrow_class_junk then
    ClF, ClFmap := NarrowClassGroup(F);
    ClFelts := [ cl : cl in ClF ];
    ClFreps := [ cl @ClFmap : cl in ClFelts ]; assert ClFreps[1] eq 1*OF;
    ridls_norms_classes := [Norm(I) @@ClFmap : I in ridls];
    inds := [Index(ClFelts, NI) : NI in ridls_norms_classes];

    // For each pair of ridls I,J find a generator of the pid R*Norm(I)/Norm(J) where R is in ClFreps 
    ridls_norms_gens       :=  [F| 0 : i in [1..h]];
    ridls_colon_norms_gens := [[F| 0 : i in [1..h]] : j in [1..h]];
    ClF_reps_diffs_gens    := [[F| 0 : i in [1..#ClFreps]] : j in [1..#ClFreps]];
    // Find generators of Cij/rep(Cij) where Cij is rep[i]/rep[j]
    for j,i in Seqset(inds) do 
      if i eq j then
        ClF_reps_diffs_gens[j][i] := F!1;
      else
        Q := ClFreps[i]/ClFreps[j];
        R := ClFreps[r] where r is Index(ClFelts, ClFelts[i]-ClFelts[j]);
        _, g := IsNarrowlyPrincipal(Q/R : real_places:=real_places, UnitRealValuations:=UnitRealValuations);
        ClF_reps_diffs_gens[j][i] := F!g;
      end if;
    end for;
    vprintf ModFrmHil: "Computing generators for norms of right ideal classes ... "; 
    vtime ModFrmHil:
    for i := 1 to h do 
      ii := Index(ClFelts, -ridls_norms_classes[i]);
      _, g := IsNarrowlyPrincipal(ClFreps[ii]*Norm(ridls[i]) : real_places:=real_places, 
                                                               UnitRealValuations:=UnitRealValuations);  
      ridls_norms_gens[i] := F!g;
    end for;
    for j,i in [1..h] do
      ii := Index(ClFelts, -ridls_norms_classes[i]);
      jj := Index(ClFelts, -ridls_norms_classes[j]);
      ridls_colon_norms_gens[j][i] := (i eq j) select 1 else
                                      ridls_norms_gens[i]/ridls_norms_gens[j] / ClF_reps_diffs_gens[jj][ii];
    end for;
    if debug then // check by doing it the straightforward O(h^2) way 
      for j,i in [1..h] do 
        R := ClFreps[r] where r is Index(ClFelts, ridls_norms_classes[j]-ridls_norms_classes[i]);
        bool, g := IsNarrowlyPrincipal(R*Norm(ridls[i])/Norm(ridls[j]) : real_places:=real_places,
                                                                         UnitRealValuations:=UnitRealValuations);  
        assert bool and g*OF eq g1*OF where g1 is ridls_colon_norms_gens[j][i];
      end for; 
    end if;

    OH`RightIdealClasses[record_idx]`rids_narrow_class_junk := 
      [* ClF, ClFmap, ClFelts, ClFreps, ridls_norms_classes, inds, ridls_norms_gens, ridls_colon_norms_gens *];
  end if; // assigned junk
  // Look up junk
  ClF, ClFmap, ClFelts, ClFreps, ridls_norms_classes, _, _, ridls_colon_norms_gens 
    := Explode(OH`RightIdealClasses[record_idx]`rids_narrow_class_junk);

  if use_theta then
    // Try to quickly determine the class of the left order of each subideal using theta series.  
    // This reduces the number of ideal-isomorphism tests, but means we have to compute the left orders + thetas. 
    ords_forms := [ [j[2],j[3]] where j is junk_for_IsIsomorphic(LO) : LO in ords ];
    /* TO DO: use values of short vectors somehow ... it's yielded nothing so far!
    ords_grams := [ T*j[5]*Transpose(T) where T is Parent(j[5])!j[4] 
                                        where j is junk_for_IsIsomorphic(LO) : LO in ords ];
    */
    // Note: LO`thetas[1] now computed in RightIdealClassesAndOrders
    if not &and [assigned LO`thetas : LO in ords] then
      // check if the second forms are pos def (TO DO: should we arrange this by taking 'a' totally positive?)
      js := &and[ IsPositiveDefinite(forms[2]) : forms in ords_forms ] select [1,2] else [1];
      ords_lats := [ [LatticeWithGram(ords_forms[i,j] : CheckPositive:=false) : j in js] : i in [1..#ords] ];
      dim := 4*Degree(F); 
      Vol1 := Pi(RealField())^(dim/2) / Gamma(dim/2 + 1); // = volume of unit sphere of this dimension
      Det_size := Min([ Determinant(ords_forms[i][1]) : i in [1..#ords] ]);
      theta_prec := Ceiling( (100 * Sqrt(Det_size) / Vol1) ^ (2/dim) );
      g := GCD([gcd_of_quad_form(ords_forms[i,j]) : i in [1..#ords], j in js]); // lazy
      theta_prec := (theta_prec div g) * g; // TO DO: ThetaSeries should be smart enough to figure this out!
      // get theta coefficients up to and including theta_prec
      vprintf ModFrmHil: "Computing theta series to precision %o ... ", theta_prec; 
      vtime ModFrmHil:
      for i := 1 to #ords do
        ords[i]`thetas := [ThetaSeries(ords_lats[i,j], theta_prec) : j in js]; end for;
      vprint ModFrmHil, 3: "Theta series of the left orders are", &cat [LO`thetas : LO in ords];
    else // need js below (this is hacky)
      js := [1..#ords[1]`thetas];
      assert &and [#LO`thetas eq #js : LO in ords];
    end if;
    ords_thetas := [LO`thetas : LO in ords];
    // reset theta_prec to the minimum that distinguishes these pairs of (partial) theta series
    // TO DO: haven't done it properly for pairs 
    theta_prec := 1;
    for j := 1 to #ords_thetas[1] do 
      coeffs := [ [Coefficient(th,n) : n in [1..AbsolutePrecision(th)-1]] where th is thetas[j] 
                                                                         : thetas in ords_thetas ];
      coeffs := Sort(Setseq(Seqset(coeffs))); // sort the distinct thetas lexicographically
      for k := 2 to #coeffs do 
        i := Min([i : i in [1..#coeffs[k]] | coeffs[k-1][i] ne coeffs[k][i] ]); 
        theta_prec := Max(theta_prec, i);
      end for;
    end for;
    vprintf ModFrmHil, 2: "Using theta series to precision %o (the %o orders have %o distinct series)\n", 
                           theta_prec, #ords, #Seqset(ords_thetas);
    /* Also use the values of f2 on short vectors of f1 to distinguish pairs 
    ords_short_vals := [* *];
    vprintf ModFrmHil, 1: "Listing values on short vectors ... ", theta_prec; 
    vtime ModFrmHil, 1:
    for i := 1 to #ords_forms do 
      // look at the second positive integer that is represented by the first form
      // (no point considering the first because shortest vectors are exactly the units of norm 1)
      assert theta_prec lt 2*Degree(F) or Minimum(ords_lats[i,1]) eq 2*Degree(F); // just to make sure
      N := 2*Degree(F) + 1;
      while N le theta_prec do 
        if Coefficient(ords_thetas[i,1], N) gt 0 then break; end if;
        N +:= 1;
      end while;
      if N gt theta_prec or Coefficient(ords_thetas[i,1], N) gt 100 then 
        Append( ~ords_short_vals, {});
        continue i;
      end if;
      svs := [ sgn*Matrix(sv[1]) : sv in ShortVectors(ords_lats[i,1], N), sgn in [1,-1] ];
      //Append( ~ords_short_vals, Sort([ (sv*ords_forms[i,2]*Transpose(sv))[1,1] : sv in svs ]) );
      svs_vals := [ (sv*ords_grams[i]*Transpose(sv))[1,1] where sv is ChangeRing(sv,F) : sv in svs ];
      svs_vals := { <x, #[y: y in svs_vals | y eq x] > : x in Seqset(svs_vals) }; 
      Append( ~ords_short_vals, svs_vals);
    end for; // i
ii := Min([i : i in [1..#ords] | #ords_short_vals[i] gt 0 ] cat [1]);
"The short values are (sample only): ", ords_short_vals[i]; 
    */
  end if; // use_theta

  // seems always faster to use_Jprime for the colon calculation 
  // instead of ColonInternal
  // However ... the basis obtained when we use_Jprime seems worse,
  // so the lattice enumeration step then takes longer, eg
  // around 20% longer for the real subfield of Q(zeta_25) of degree 10.
  // The enumeration cost dominates running time for degree > 8.
  use_Jprime := Degree(F) le 8; 
  if use_Jprime then  
    if debug then   // make sure ridls are integral ideals, as the Jprime trick assumes
      for J in ridls do assert &and [zb in OJ : zb in ZBasis(J)] where OJ is RightOrder(J); end for;
    end if;
    ps := LCM([NP] cat [Integers()| Norm(Norm(J)) : J in ridls ]); 
    vprintf ModFrmHil, 3: "Getting JJs ... ";  
    vtime ModFrmHil, 3:
    JJs := [ <JJ,b,P> where JJ,b,P is Jprime(J : coprime_to:=ps) : J in ridls ]; 
  end if;

    // (previously) loop over several Ps started here

    bool, tps := IsDefined(OH`RightIdealClasses[record_idx]`tps, P);
    if not bool then
      tps := AssociativeArray(CartesianProduct([1..h],[1..h]));
    end if;
      
    Pclass := P @@ ClFmap;
    Pclassrep := ClFreps[r] where r is Index(ClFelts, Pclass);
    bool, gP := IsNarrowlyPrincipal(P/Pclassrep : real_places:=real_places, 
                                    UnitRealValuations:=UnitRealValuations);  assert bool;
    gP := F!gP;
    function inds_for_j(j)
      b := ridls[j];
      NormbP := Norm(ridls[j])/P; // = Norm(bP) for each bP below
      NormbP_class := ridls_norms_classes[j] - Pclass;
      inds := [i : i in [1..h] | ridls_norms_classes[i] eq NormbP_class];
      return inds, b, NormbP, NormbP_class;
    end function;

    if eP eq 1 then
      vprintf ModFrmHil: "Getting tp's for prime of norm %o (using \"%o prime method\")\n", 
                          NP, small_prime select "small" else "large";
    else
      vprintf ModFrmHil: "Getting tp's for ideal of norm %o^%o (using \"%o prime method\")\n", 
                          NPP, eP, small_prime select "small" else "large";
    end if;
    IndentPush(); 

    if small_prime then  // quicker to run through subideals

      // Let I1, .., Ih denote the ridls.  
      // We need Ij < t^-1*Ii with norm-index P. 
      // Writing b for Ij, list the (NP+1) P-super-ideals bP of b.  
      // For each bP, find Ii and t with t*bP = Ii. 
      // Thus t is determined up to left mult by units of LeftOrder(Ii)

      for j in rows do
        inds, b, NormbP, NormbP_class := inds_for_j(j);
        vprintf ModFrmHil, 2: "Subideals"; 
        vtime ModFrmHil, 2:
        b_subideals := Subideals_of_ideal_newer(b, P : use_theta:=use_theta );
        vprintf ModFrmHil, 2: "Ideal isomorphism tests: "; time_iso := Cputime();
        numtests := 0;

        for bsub in b_subideals do 
          // Set bP := P^-1 * bsub
          bPCIs := [ Pinv*CI : CI in CoefficientIdeals(PseudoMatrix(bsub)) ] where Pinv is P^-1;
          bPmat := Matrix(PseudoMatrix(bsub));
          bP := rideal< OH | PseudoMatrix(bPCIs, bPmat) : Check:=debug >;
          if debug then assert Norm(bP) eq NormbP; 
          else bP`Norm := NormbP; end if; 
          // Figure out the class of bP as a right ideal of O
          // ie compute v in A, a in ridls such that  v*a = bP.
         /* TO DO: figure out whether this makes any sense, and fix syntax now that tps are arrays
          // Some hocus pocus to guess which inds are more likely:
          inds_nonzero := [i : i in inds | IsDefined(tps[<j,i>]) and #tps[<j,i>] gt 0]; // indices of ridls which already showed up
          if #inds_nonzero gt 0 then 
            // if some ridls tend to occur repeatedly, check those first; 
            // if they tend to occur at most once, check the others first
            avg_count := &+[#tps[<j,i>] : i in inds_nonzero] / #inds_nonzero;
            sgn := (avg_count gt 1.33 or #inds_nonzero eq 1) select 1 else -1; 
            Sort(~inds, func< i1,i2 | sgn*(#tps[<j,i2>]-#tps[<j,i1>]) >); 
          end if;
         */
          if use_theta then
            bsub_forms := [j[2],j[3]] where j is junk_for_IsIsomorphic(LeftOrder(bsub));
          //bsub_gram := T*j[5]*Transpose(T) where T is Parent(j[5])!j[4] 
          //                                 where j is junk_for_IsIsomorphic(LeftOrder(bsub)); 
            bsub_lats := [ LatticeWithGram(f : CheckPositive:=false) : f in bsub_forms[js] ];
            vprintf ModFrmHil,3: "ThetaSeries ... "; 
            vtime ModFrmHil,3:
            bsub_thetas := [ ThetaSeries(L, theta_prec) : L in bsub_lats ];
  /* skip this for now, because it doesn't help with the Gross example (or indeed any example I've seen yet!)
    assert Minimum(bsub_lats[1]) eq 2*Degree(F);
            N := 2*Degree(F) + 1;
            while N le theta_prec do 
              if Coefficient(bsub_thetas[1], N) gt 0 then break; end if;
              N +:= 1;
            end while;
            if N gt theta_prec or Coefficient(bsub_thetas[1], N) gt 100 then 
              bsub_short_vals := {};
            else
              svs := [ sgn*Matrix(sv[1]) : sv in ShortVectors(bsub_lats[1], N), sgn in [1,-1] ];
              //bsub_short_vals := Sort([ (sv*bsub_forms[2]*Transpose(sv))[1,1] : sv in svs ]);
              svs_vals := [ (sv*bsub_gram*Transpose(sv))[1,1] where sv is ChangeRing(sv,F) : sv in svs ];
              bsub_short_vals := { <x, #[y: y in svs_vals | y eq x] > : x in Seqset(svs_vals) }; 
            end if;
  */
          end if;
          found_class := false; 
          for i in inds do
            // quickly try to rule out some order classes (by looking at short vectors of the pair of forms)
            if use_theta then 
              io := order_indices[i];
              for j in js do
                if Valuation(bsub_thetas[j] - ords_thetas[io,j]) le theta_prec then 
                  continue i; 
                end if; 
              end for;
              /*
              if bsub_short_vals ne ords_short_vals[io] then
                "short vals don't match"; 
                continue i; 
              end if;
              */
            end if;
            numtests +:= 1;
            if use_Jprime then
              // scale to make ideal integral, since the Jprime trick assumes this
              bool, v := IsIsomorphicInternal(NP*bP, ridls[i] : real_places:=real_places,
                                                                UnitRealValuations:=UnitRealValuations,
                                                                JJ:=JJs[i] );
              if bool then v *:= NP; end if;
            else                                                         
              bool, v := IsIsomorphicInternal(bP, ridls[i] : real_places:=real_places,
                                                             UnitRealValuations:=UnitRealValuations );
            end if;
            if bool then
              if debug then assert ridls[i] eq v*bP; end if;
              ji := <j,i>;
              if IsDefined(tps, ji) then
                Append(~tps[ji], v); 
              else
                tps[ji] := [v]; 
              end if;
              error if found_class, "This ideal is in more than one class!!!\n", bP; // only caught in debug
              found_class := true; 
              if not debug then break i; end if;
            end if;
          end for; // i
          error if not found_class, "Failed to find isomorphism class for right ideal\n", bP;
        end for; // bsub
        vprintf ModFrmHil, 2: "needed %o tests; time for row = %o sec\n", numtests, Cputime(time_iso);

        for subI in b_subideals do  // these ideals are gonna get deleted, make sure stored data gets deleted too
         if assigned subI`LeftOrder then 
          delete subI`LeftOrder`junk_for_IsIsomorphic; end if; end for;
      
     end for; // j
   end if;
   if not small_prime then  // NP large relative to h ==> quicker to run through ideal classes

      // Let I1 .. Ih denote the ridls.  For each pair Ij, Ii, we list all t in H 
      // with t*Ij < Ii and Norm(t*Ij) = P*Norm(Ii), up to mult by scalars, 
      // and then choose reps for t modulo left mult by units of LeftOrder(Ii)

      ts_raw := []; // ts_raw[j] will contain raw ts for the jth row
     
      ridls_colonZBs := OH`RightIdealClasses[record_idx]`rids_colonZBs; 

      for j := 1 to h do 
        if j notin rows then
          Append(~ts_raw, [[] : i in [1..h]]);
          continue;
        end if;

        inds := inds_for_j(j);

        // Make sure we know Z-bases for (I:J)'s
        for i in inds do 
          // Get a totally positive generator g of the ideal (there exists one, for i in inds)
          if not IsDefined(ridls_colonZBs, <j,i>) then
            vprintf ModFrmHil,3: "Z-basis for I:J (%ousing the J' trick) ... ", 
                                                   use_Jprime select "" else "not "; 
            vtime ModFrmHil,3:
            if use_Jprime then 
              JJ, b := Explode(JJs[j]);  // [I : J] = I * J^-1 = I * JJ * b^-1
              IJJ_ZB := IntersectionZBasis(ridls[i], JJ);
              ridls_colonZBs[<j,i>] := [H| x*binv : x in IJJ_ZB ] where binv is b^-1;
            else
              icolonj := ColonInternal(PseudoMatrix(ridls[i],H), PseudoMatrix(ridls[j],H), H, true // left multipliers
                                       : Hermite:=false); 
              ridls_colonZBs[<j,i>] := ZBasis(icolonj, H);
            end if;
          end if;
        end for; // i in inds

        vprintf ModFrmHil, 2: "Doing row #%o:  ", j;
        time_row := Cputime();

        if debug then
          for i in inds do
            g := ridls_colon_norms_gens[j][i]*gP;
            assert g*OF eq Norm(ridls[i])/Norm(ridls[j])*P;
          end for;
        end if;

        ts_raw_j := [[] : i in [1..h]];
        for i in inds do
          g := ridls_colon_norms_gens[j][i] * gP;
          for u in pos_units_mod_norms[i] do
            bool, elts := has_element_of_norm(ridls_colonZBs[<j,i>], u*g : all);
            if bool then 
              Append(~ts_raw_j[i], elts); 
            end if;
          end for;
        end for;
        Append(~ts_raw, ts_raw_j); assert #ts_raw eq j;
       
        vprintf ModFrmHil, 2: "Time for row #%o: %o\n", j, Cputime(time_row);

      end for; // j

      OH`RightIdealClasses[record_idx]`rids_colonZBs := ridls_colonZBs; // update cache (note: this might use a lot of memory!)

      // We've computed ts_raw[j][i] for all (relevant) j and i
      // Now choose one from each orbit under left action of units

      // Choose well-defined reps mod +-1 
      function normalize(S)
        return {-s lt s select -s else s : s in S};
      end function;

      inds := [(j in rows) select inds_for_j(j) else [] : j in [1..h]];
      allinds := Seqset(&cat inds);
      noums := AssociativeArray(allinds);
      for i in allinds do 
        noumsi := ridls[i]`LeftOrder`norm_one_units_mod_scalars;
        assert Universe(noumsi) eq H;
        Exclude(~noumsi, H!1);
        Exclude(~noumsi, H!-1);
        noums[i] := noumsi;
      end for;

      vprintf ModFrmHil, 2: "Choosing representatives modulo left multiplication by units: ";
      vtime ModFrmHil, 2:

      for j in rows do
        for i in inds[j] do 
          ts := [H| ];
          for ie := 1 to #ts_raw[j][i] do 
            elts := ts_raw[j][i][ie]; 
            us := noums[i];
            // Discard repeats modulo left mult by the norm-one-units us;
            // here elts contains full orbits mod +-1,
            // and us are the units mod +-1
            length := 1+#us;
            if length eq 1 then
              ts cat:= elts;
            elif #elts eq length then
              Append(~ts, elts[1]);
            else
              elts := normalize(elts);
              while true do
                // assert #elts ge length;
                // assert #elts mod length eq 0;
                e1 := Rep(elts);
                Append(~ts, e1);
                if #elts eq length then
                  // the current elts form precisely one orbit
                  break;
                else
                  Exclude(~elts, e1);
                  orbit := normalize({H| u*e1 : u in us});
                  // assert orbit subset elts;
                  elts diff:= orbit;
                end if;
              end while;
            end if;
          end for; // ie

          if debug and small_prime then // this checks the two methods against eachother
            bool, tpsji := IsDefined(tps, <j,i>); assert bool;
            assert #ts eq #tpsji;
            for t in ts do 
              assert #[tt : tt in tpsji | tt/t in  LeftOrder(ridls[i])] eq 1; 
            end for;
            for t in tpsji do 
              assert #[tt : tt in ts | tt/t in  LeftOrder(ridls[i])] eq 1; 
            end for;
          end if;

          tps[<j,i>] := ts;
        end for; // i
      end for; // j

    end if; // small_prime
    IndentPop();

    // Sanity checks
    // (we really need the first check, it actually once failed for a huge prime p)
    keys := Keys(tps);
    for j in rows do
      assert &+ [#tps[<j,i>] : i in [1..h] | <j,i> in keys] eq num; 
    end for; 
    if debug then
      if rows eq [1..h] then
        tps0 := OH`RightIdealClasses[record_idx]`tps;
        tps_rows0 := OH`RightIdealClasses[record_idx]`tps_rows;
        TP := Matrix(h, [Integers()| IsDefined(tps,<j,i>) select #tps[<j,i>] else 0 : i,j in [1..h]]);
        for P0 in Keys(tps0) do
          if tps_rows0[P0] eq [1..h] then
            TP0 := Matrix(h, [Integers()| IsDefined(tps0[P0],<j,i>) select #tps0[P0][<j,i>] else 0 : i,j in [1..h]]);
            assert TP*TP0 eq TP0*TP;
          end if;
        end for; 
      end if;
    end if;

    OH`RightIdealClasses[record_idx]`tps[P] := tps;
    bool, old_rows := IsDefined(OH`RightIdealClasses[record_idx]`tps_rows, P);
    OH`RightIdealClasses[record_idx]`tps_rows[P] := bool select Sort(old_rows cat rows) else rows;

    // (previously) loop over several Ps ended here
    
  IndentPop();
  vprint ModFrmHil: "Precomputation time:", Cputime(time0);
end procedure;

// Choose 'Support' for RightIdealClasses.
// Take primes not dividing Level(M), with extra properties as specified

function support_for_rids(M : norm_gt:=1, coprime_to:=1, num:=1)
  N := coprime_to * Level(M);
  OA := QuaternionOrder(M);
  ZF := BaseRing(OA);
  F := NumberField(ZF);
  ClF, cl := NarrowClassGroup(F);
  Support := [];
  S := sub<ClF| >;
  q := norm_gt;
  inc := 50;
  while true do
    primes := [Q : Q in PrimesUpTo(q+inc, F) | Norm(Q) gt q and Norm(Q+N) eq 1];
    //primes := [Q : Q in primes | IsPrime(Norm(Q))]; // only use degree 1 (why?)
    for Q in primes do 
      Qcl := Q @@ cl;
      if Qcl notin S or S eq ClF then
        S := sub<ClF| S, Qcl>;
        Append(~Support, Q);
        if #Support ge num and S eq ClF then 
          return Support; 
        end if;
      end if;
    end for;
    q +:= inc;
  end while;
end function;

// Access or compute right ideal classes
// !! ALWAYS ACCESS/CACHE THE RIGHT IDEAL REPS FOR M VIA THIS !!

function get_rids(M)
  if assigned M`rids then 
    return M`rids;
  elif assigned M`Ambient then
    return get_rids(M`Ambient);
  end if;

  OA := QuaternionOrder(M);
  OK := BaseRing(OA);
  one := 1*OK;
  N := Level(M);

  // Use stored rids if their support is prime to Level(M)
  if assigned OA`RightIdealClasses then
    for rec in OA`RightIdealClasses do 
      if forall {P : P in rec`support | P + N eq one} then
        M`rids := rec`rids;
        return M`rids;
      end if;
    end for;
  end if;

  // If stored rids have wrong support, convert them to rids with suitable support 
  if assigned OA`RightIdealClasses and #OA`RightIdealClasses gt 0 then
    supp1 := OA`RightIdealClasses[1]`support;
    rids1 := OA`RightIdealClasses[1]`rids;
    // convert_rids assumes support coprime to support of rids1
    // TO DO: what num to use here? using more than 1, to avoid deep searches (hopefully)
    support := support_for_rids(M : coprime_to := &*supp1, 
                                    num := Floor(Sqrt(Degree(OK))) );
    M`rids := convert_rids(rids1, support);
    return M`rids;
  end if;

  // Computing rids for OA for the first time
  support := support_for_rids(M : norm_gt:=1);
  M`rids := RightIdealClassesAndOrders(OA : Support:=support,
                                            compute_order_classes:=false);
  return M`rids;
end function;

function get_tps(M, p : rows:=0)
  return get_tps_for_rids(QuaternionOrder(M), get_rids(M), p : rows:=rows);
end function;

function get_tps_for_rids(OA, rids, p : rows:=0)
  h := #rids;
  if rows cmpeq 0 then
    rows := [1..h];
  else
    assert Type(rows) eq SeqEnum and rows subset [1..h];
  end if;
  new_rows := rows;

  // Check if tps are cached for these rids
  // (Locating the rids_record this way is a silly vestigial thing)
  idx := 1; 
  while idx le #OA`RightIdealClasses do 
    rec := OA`RightIdealClasses[idx];
    if IsIdentical(rids, rec`rids) then
      if not assigned rec`tps then
        break;
      end if;
      bool, tps_p := IsDefined(rec`tps, p);
      if bool then 
        bool, old_rows := IsDefined(rec`tps_rows, p); assert bool;
        if rows subset old_rows then
          return tps_p;
        else
          new_rows := [i : i in rows | i notin old_rows];
        end if;
      end if;
      break;
    end if;
    idx +:= 1;
  end while;
  error if idx gt #OA`RightIdealClasses, "There should be a record for these rids!";

  if assigned rec`rids1 then
    // rids were converted from rids1, by left-multiplying by elts
    // (rids1 and rids_conversion are assigned together by convert_rids)
    rids1 := rec`rids1;
    elts := rec`rids_conversion;
    if debug then
      assert forall{i: i in [1..#rids] | rids[i] eq elts[i]*rids1[i]};
    end if;
    // Policy: always compute and cache tps on rids1 
    // because rids1 are likely to be used for most levels
    // (and usually the first record in OA`RightIdealClasses).
    // Don't cache the converted tps, they take far too much memory!
    tps1 := get_tps_for_rids(OA, rids1, p : rows:=rows);
    vprintf ModFrmHil, 2: "Converting tp's for prime of norm %o: ", Norm(p);
    vtime ModFrmHil, 2:
    tps := convert_tps(tps1, elts, rows);
    return tps;
  end if;

  // prepare record to be used in precompute_tps
  if not assigned rec`rids_colonZBs then
    rec`rids_colonZBs := AssociativeArray(CartesianProduct([1..h],[1..h]));
  end if;
  if not assigned rec`tps then 
    rec`tps := AssociativeArray(PowerIdeal(Order(p)));
    rec`tps_rows := AssociativeArray(PowerIdeal(Order(p)));
  end if;
  OA`RightIdealClasses[idx] := rec;

  precompute_tps(OA, p, rids, idx, new_rows); 
  // This caches them in OA`RightIdealClasses[idx]`tps[p], 
  //    and also updates OA`RightIdealClasses[idx]`tps_rows[p]

  return OA`RightIdealClasses[idx]`tps[p];
end function;

/******************************************
* from proj1.m
*******************************************/

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



/********************************************************
* from Algebra/AlgAss/enum.m
*********************************************************/

// Caching: O`RightIdealClasses is a list of records with this format.
// (Also used to store data for the Hilbert modular forms precomputation)

rids_record := recformat< orders:SeqEnum,    // a list of conjugacy classes of Orders 
                          rids:SeqEnum,      // a list of RightIdealClasses
                          support:SeqEnum,   // primes dividing the norms of the rids

                          rids1:SeqEnum,     // rids were obtained by converting from rids1
                          rids_conversion:SeqEnum, 

                          tps:Assoc,         // array with values [[tps_ij:i]:j]
                          tps_rows:Assoc,    // array recording which rows of tps have been computed
                          rids_colonZBs:Assoc,      // used in precompute_tps
                          rids_narrow_class_junk:List // ""
                        >;

/////////////////////////////////////////////
// Silly functions

function mult_no_check(I1,I2 : Sides:="Both")
  return '*'(I1,I2 : Check:=false, Sides:=Sides);
end function;

function grpab_to_string(C)
  c := Invariants(C);
  if c eq [] then
    return "trivial";
  end if;
  s := "";
  for i := 1 to #c do
    s *:= "Z";
    if c[i] ne 0 then s *:= "/"*IntegerToString(c[i]); end if;
    if i lt #c then s *:= " + "; end if;
  end for;
  return s;
end function;

///////////////////////////////////////////////
// Helper functions to work with the norm form

function GramMatrixofAlgebra(A)
  if not assigned A`GramMatrix then
    B:= Basis(A);
    A`GramMatrix:= SymmetricMatrix( [ Trace( B[i]*Conjugate(B[j])) : i in [1..j], j in [1..4] ] );
  end if;
  
  return A`GramMatrix;
end function; 

function TraceFormsOnQBasis(A)
  if not assigned A`TraceFormsOnQBasis then 
    F := BaseRing(A);  
    M := GramMatrixofAlgebra(A);
    B := [ A | b*f : f in AbsoluteBasis(F), b in Basis(A) ];
    B := Matrix([ Eltseq(b) : b in B ]);
    T := B * M * Transpose(B);
    d:= Nrows(T);
    T1 := Matrix(Rationals(), d, d, [AbsoluteTrace(x) : x in Eltseq(T)] );
    AF:= AbsoluteField(F);
    a:= PrimitiveElement(AF);
    ok, den := IsIntegral(a);
    if not ok then a*:= den; end if;
    a:= F ! a; 
    T2 := Matrix(Rationals(), d, d, [AbsoluteTrace(a*x) : x in Eltseq(T)] );
    A`TraceFormsOnQBasis := [T1, T2];
  end if;

  return Explode(A`TraceFormsOnQBasis);
end function;

function GramMatrices(O: LLL:= false, a:= 0)
  A:= Algebra(O);
  K:= BaseField(A);

  if K eq Rationals() then
    Grams:= [GramMatrix(O)];
    B:= Basis(O);
  else
    B:= ZBasis(O);
    if a cmpeq 0 then a:= AbsoluteField(K).1; end if;
    if not IsIntegral(a) then a *:= Denominator(a); end if;
    
    GramOverF:= M * GramMatrixofAlgebra(A) * Transpose(M) where M:= Matrix(B);
    Grams:= [ Matrix( Integers(), #B, [ AbsoluteTrace(  x): x in Eltseq(GramOverF)]),
              Matrix( Integers(), #B, [ AbsoluteTrace(a*x): x in Eltseq(GramOverF)]) ];
  end if;

  if LLL then
    F, T:= LLLGram( Grams[1] : Delta:= 0.999, Proof:= false);
    Grams:= [ F ] cat [ T * g * Transpose(T) : g in Grams[2..#Grams] ];
    B:= [ &+[ T[i,j] * B[j] : j in [1..#B] | T[i,j] ne 0]: i in [1..#B] ];
  end if;
 
  return Grams, B;
end function;

////////////////////////////////////////////////////////////////
// Order classes and ideal classes

ListPrimes:= function(R, Num, D)
  case Type(R):
    when RngInt:
      List:= [];
      p:= 1;
      repeat
        p:= NextPrime(p);
        if D mod p ne 0 then Append(~List, <p,p>); end if;
      until #List ge 5;
      return List, [];

    when RngUPol:
      List:= [];
      k:= BaseRing(R);
      i:= 1;
      repeat
        L:= AllIrreduciblePolynomials(k, i);
        for f in L do
          if Valuation(D, f) eq 0 then Append(~List, <f,f>); end if;
        end for;
        i +:= 1;
      until #List ge 5;
      return List, [];

  else
    NCl, h:= NarrowClassGroup(R);
    // we need prime ideals that generate this group, at least modulo the norms of the twosided ideals
    S:= sub< NCl | 2*NCl, [(f[1]) @@ h : f in Factorization(D) | IsOdd(f[2]) ] >;
    RayClassPrimes:= [];
    // now look for ideals with small norm
    p:= 1;
    while #S ne #NCl do
      p:= NextPrime(p);
      for f in Decomposition(R, p) do
        if (Valuation(D, f[1]) eq 0) and (f[1] @@ h) notin S then
          Append(~RayClassPrimes, <f[1], p>);
          S:= sub< NCl | S, f[1] @@ h >;
          if #S eq #NCl then break; end if;
        end if;
      end for;
    end while;

    // choose the smallest odd split primes not dividing D
    Primes:= [];
    p := 2;
    while #RayClassPrimes + #Primes lt Num do 
      p := NextPrime(p);
      for f in Decomposition(R, p) do
        P := f[1];
        if RamificationDegree(P) eq 1 and InertiaDegree(P) eq 1 and
           Valuation(D,P) eq 0 and (<P,p> notin RayClassPrimes) then 
          Append(~Primes, < Norm(f[1]), f[1], p >);
        end if;
        if #RayClassPrimes + #Primes ge Num then break; end if;
      end for;
    end while;

    // Sort by the number of maximal right ideals we will get
    Primes:= [ <P[2], P[3]>: P in Sort(Primes) ];

    return Primes, RayClassPrimes;
  end case;
end function;

get_coords:= function(O, p)
  if Type(O) eq AlgQuatOrd then
    B:= Basis(O);
    pO:= ideal< O | p >; 
  else
    B:= LocalBasis(O, p : Type:= "Submodule");
    B:= ChangeUniverse(B, O);
    pO:= ideal< O | Generators(p) >;
  end if;
  A:= Algebra(O);
  BI:= Matrix([Eltseq(A ! b) : b in B] )^-1;
  k, h:= ResidueClassField(p);
  T:= Matrix(k, 1, [ Trace(B[i]) @ h : i in [1..4] ]);
  P:= PolynomialRing(k);
  v:= Valuation(Discriminant(O), p);

  found:= false;
  repeat
    e:= &+[ B[i] * (Random(k) @@ h) : i in [1..4] ];
    m:= P ! [ x @ h : x in Eltseq(MinimalPolynomial(e)) ];
    roots:= Roots(m);
    if #roots eq 2 then
      e:= (e - (roots[1,1] @@ h)) * (((roots[2,1] - roots[1,1])^-1) @@ h);
      S:= HorizontalJoin(T, Matrix( [ [ v[j] @ h : j in [1..4] ] where v:= Vector(Eltseq(A ! (B[i] * e))) * BI : i in [1..4] ] ));
      K:= Kernel(S);
      assert Dimension(K) eq 1;
      x:= &+ [e[i] @@ h *B[i] : i in [1..4] | e[i] ne 0] where e:= Eltseq(K.1);
      found := true;
    elif v eq 0 and #roots eq 1 and roots[1,2] eq 2 then
      x:= e - (roots[1,1] @@ h);
      if x notin pO then
        S:= HorizontalJoin(T, Matrix( [ [ v[j] @ h : j in [1..4] ] where v:= Vector(Eltseq(A ! (x * B[i]))) * BI : i in [1..4] ] ));
        s:= Solution(S, Vector(k, [1,0,0,0,0]));
        e:= &+ [ee[i] @@ h *B[i]  : i in [1..4] | ee[i] ne 0] where ee:= Eltseq(s);
        found:= true;
      end if;
    end if;
  until found;

  // now wlog. e and x map to the upper entries of M(2,k)
  f:= 1-e;
  S:= HorizontalJoin(T, Matrix( [ [ v[j] @ h : j in [1..4] ] where v:= Vector(Eltseq(A ! (B[i] * f))) * BI : i in [1..4] ] ));
  K:= Kernel(S);
  assert Dimension(K) eq 1;
  y:= &+ [e[i] @@ h *B[i]  : i in [1..4] | e[i] ne 0] where e:= Eltseq(K.1);

  if v eq 0 then
    // Let's get a ring isomorphism O/pO -> M(2,k). Wlog. only y is off by a scalar.
    y*:= ((Trace(x*y) @ h)^-1) @@ h;
  end if;

  assert not debug or ([e,x,y,f] subset O);

  return e, x, y, f;
end function;

function theta_series(O : prec:=0)
  if assigned O`thetas and AbsolutePrecision(O`thetas[1]) gt prec then
    return O`thetas[1];
  end if;

  M := junk_for_IsIsomorphic(O)[2];
  L := LatticeWithGram(M);

  if prec eq 0 then
    // choose a number of terms that won't take too long
    dim := 4*Degree(BaseRing(O));
    Vol1 := Pi(RealField())^(dim/2) / Gamma(dim/2 + 1); // = volume of unit sphere of this dimension
    prec := Ceiling( (100 * Sqrt(Determinant(M)) / Vol1) ^ (2/dim) );
  end if;

  // TO DO: ThetaSeries should be smart enough to do this itself!
  g := GCD([M[i,i] : i in [1..Nrows(M)]] cat [2*m : m in Eltseq(M)]);
  prec1 := (prec div g) * g;
  theta := ThetaSeries(L, prec1);
  assert AbsolutePrecision(theta) ge prec1+1;
  ChangePrecision(~theta, prec+1);

  O`thetas := [theta];
  return theta;
end function;

function IsIsomorphic1(O1, O2 : FindElement:= false, ConnectingIdeal:= 0)

  A:= Algebra(O1);
  K:= BaseField(A);

  if Type(K) eq FldFunRat then return IsIsomorphic(O1, O2 : FindElement:= FindElement); end if;
  
  if IsDefinite(A) /* and AbsoluteDegree(K) le 5*/ then
    if Type(K) eq FldRat then 
      ok:= IsIsomorphic(O1, O2);
      if ok and FindElement then
        h, x:= Isomorphism(O1, O2); 
        return true, h, x;
      end if;
      return ok, _, _;
    end if;
    
    B1, FF1, FF2 := Explode(junk_for_IsIsomorphic(O1)); // stored on O1
    B2, GG1, GG2 := Explode(junk_for_IsIsomorphic(O2));

    ok, T:= IsIsometric( [FF1, FF2], [GG1, GG2] );

    if ok and FindElement then
      B:= Basis(A);
      C1:= Matrix(K, [ Eltseq(A ! b): b in B1]); 
      C2:= Matrix(K, Coordinates(B, B2));
      // H describes an isometry \phi of O2 to O1 wrt. B
      H:= C2 * Matrix(K, T) * C1;

      // \phi(1) is a unit in O1. Change this to \phi(1)=1.
      e:= A ! H[1];
      if not IsOne(e) then
        // print "correcting unit";
        e:= 1/e; 
        H:= H * Matrix(K, [ Eltseq(e*b): b in B ]);
      end if;

      // If H describes a K - antiautomorphism, take conjugates.
      // assuming that B[1] = 1.
      if (A ! (Vector(Eltseq(B[2] * B[3])) * H)) ne  A ! H[2] * A ! H[3] then 
        // print "taking conjugates";
        H:= H * Matrix(K, [ Eltseq(Conjugate(b)): b in B ]);
      end if;

      // now H describes a K-algebra-automorphism. I.e. it is given by conjugation.
      h:= hom< A -> A | [ A ! H[i]: i in [1..4] ] >;
      KK:= Kernel(  Matrix([ &cat [Eltseq(b * c - h(c) * b): c in B] : b in B]));
      // this should never happen
      error if Dimension(KK) eq 0, "could not find conjugating element";
      x:= A ! KK.1;

      assert O2 eq O1^x;

      return true, hom< O1 -> O2 | t:-> x^-1 * t * x, s:-> x*s*x^-1 >, x;
    end if;
    return ok, _, _;
  end if;	// IsDefinite

  if ConnectingIdeal cmpeq 0 then 
    error if not IsMaximal(O1), "In indefinite algebras, this is currently implemented for maximal orders only. Sorry.";
    ConnectingIdeal:= lideal< O1 | [x * y : x in Generators(O1), y in Generators(O2) ] >;
  else
    error if LeftOrder(ConnectingIdeal) ne O1 or RightOrder(ConnectingIdeal) ne O2,
	 "ConnectingIdeal must have left order O1 and right order O2";
    // This is funny..., why can't ideals be just lattices ???
    if Order(ConnectingIdeal) ne O1 or not IsLeftIdeal(ConnectingIdeal) then
      ConnectingIdeal:= lideal< O1 | Generators(ConnectingIdeal) >;
      ConnectingIdeal`LeftOrder := O1;
      ConnectingIdeal`RightOrder:= O2;
    end if;
  end if;
    
  if not FindElement then
    if K cmpeq Rationals() then return true, _, _; end if;
    _, inf:= RamifiedPlaces(A);
    if IsEmpty(inf) then
      RCl, h:= ClassGroup(K);
    else
      RCl, h:= RayClassGroup(&+inf);
    end if;
    TwoSided:= sub< RCl | 2*RCl, [ (f[1]) @@ h : f in FactoredDiscriminant(O1) | IsOdd(f[2]) ] >;
    return Norm(ConnectingIdeal) @@ h in TwoSided, _, _;
  end if;

  swap:= not assigned O1`TwoSidedIdealClassMaps and assigned O2`TwoSidedIdealClassMaps;
  if swap then
    temp:= O1; O1:= O2; O2:= temp;
    // as above: ConnectingIdeal:= Conjugate( ConnectingIdeal ); is WRONG, since the result
    // would be a right ideal where we need a left ideal ...
    ConnectingIdeal:= lideal < O1 | [ Conjugate(x): x in Generators(ConnectingIdeal) ] >;
    ConnectingIdeal`LeftOrder := O1;
    ConnectingIdeal`RightOrder:= O2;
  end if;

  for J in TwoSidedIdealClasses(O1) do
    if Type(O1) eq AlgQuatOrd then
      ok, _, x:= IsLeftIsomorphic(ConnectingIdeal, J);
    else
      ok, x:= IsLeftIsomorphic(ConnectingIdeal, J);
    end if;
    if ok then
      if not assigned(x) then return true, _, _; end if;
      if swap then
        return true, hom< O2 -> O1 | t:-> x * t * x^-1, s:-> x^-1*s*x>, x^-1;
      else
        return true, hom< O1 -> O2 | t:-> x^-1 * t * x, s:-> x*s*x^-1>, x;
       end if;
     end if;
  end for;
  return false, _, _;
end function;

// Set up the lattices to be used in IsIsomorphic for O = AlgAssVOrd[RngOrd]

function junk_for_IsIsomorphic(O)
    if not assigned O`junk_for_IsIsomorphic then
      // Conjugating and multiplying elements in A is rather slow. This is faster.
      A:= Algebra(O);
      B:= ZBasis(O);

      Bmat:= Matrix([ &cat [ Flat(x) : x in Eltseq(b)] : b in B ]);
      T1, T2:= TraceFormsOnQBasis(A);

      F1:= ChangeRing(Bmat * T1 * Transpose(Bmat), Integers());
      F1, T:= LLLGram(F1 : Delta:= 0.9999, Eta:=0.5001, 
                           DeepInsertions:=(Nrows(F1) le 80), Proof:= false);
      // TO DO: this is the strongest LLL, is it too much for present purposes?

      B:= [ &+[T[i,j] * B[j] : j in [1..#B]] : i in [1..#B]];

      Bmat:= Matrix(Rationals(), T) * Bmat;
      F2:= ChangeRing(Bmat * T2 * Transpose(Bmat), Integers());

      O`junk_for_IsIsomorphic:= [* B, F1, F2 *];
    end if;
    return O`junk_for_IsIsomorphic;
end function;

// This function is SUPPOSED to work over Q and F_q(X) as well 
// (i.e. it gets called from ConjugacyClasses)
// mkirschm -- Feb 2009

RightIdealClassesAndOrders:= function(O : Support:= [], strict_support:= true, 
                                          compute_order_classes:= true,
                                          avoid_IsIsometric:= false);
  A:= Algebra(O);
  F := BaseField(A);
  Z_F:= BaseRing(O);
  flat:= Type(F) in {FldRat, FldFunRat};
  error if not flat and not IsAbsoluteField(F), 
    "The base field of the algebra must be absolute.";
  if flat then
    _Support:= Type(F) eq FldRat select func< x | Set(PrimeDivisors(Integers() ! x)) >
                                   else func< x | { f[1] : f in Factorization(Z_F ! x) } >;
  else
    _,_Support := IsIntrinsic("Support");
  end if;

  // check if stored in O`RightIdealClasses, which is a list of entries [* Support, Ideals, Orders *]
  if assigned O`RightIdealClasses then
    for rec in O`RightIdealClasses do
      if (IsEmpty(Support) or rec`support subset Support) and 
         (not compute_order_classes or assigned rec`orders)
      then
        return rec`rids, rec`orders;
      end if;
    end for;
  end if;

  vprint Quaternion: "Computing RightIdealClassesAndOrders.";
  if debug then 
    vprint Quaternion: "IN DEBUG MODE";
  end if;

  if flat then
    mult:= function(I,J)
      IJ:= rideal< O | [ x*y : x in Basis(I), y in Basis(J) ] >;
      if assigned(I`Norm) and assigned(J`Norm) then IJ`Norm:= Norm(I) * Norm(J); end if;
      return IJ;
    end function;
    test_iso:= IsRightIsomorphic;
  else
    mult:= func< I, J | mult_no_check(I,J : Sides:= "Right") >;
    // initialise data to be passed to IsIsomorphicInternal 
    real_places := RealPlaces(F);
    U, Umap := pFundamentalUnits(Z_F, 2);
    Uvals := [RealValuations(real_places, Umap(U.i)) : i in [1..Ngens(U)]];
    units_vals := <U, Umap, Uvals>; 
    test_iso:= func<I, J : JJ:=0 | IsIsomorphicInternal(I, J : JJ:= JJ, real_places:= real_places, 
                                                               UnitRealValuations:= units_vals) >;
  end if;

  DA:= Discriminant(A);
  DO:= Discriminant(O);

  if IsEmpty(Support) then
    Primes, RayClassPrimes:= ListPrimes(Z_F, 1, DO); 
    Primes:= RayClassPrimes cat Primes;
    strict_support := false; // two-sided ideals will involve divisors of DO
  else
    vprint Quaternion, 2: "Support was specified to be", Support;
    if Type(Support) ne SeqEnum then
      Support := [P : P in Support];
    end if;
    if flat then
      ok, Support:= CanChangeUniverse(Support, Z_F);
      error if not ok or exists{p: p in Support | not IsPrime(p)},
           "Support must only contain prime ideals of the base ring of O.";
    else
      error if not forall{p: p in Support | IsPrime(p) and Order(p) cmpeq Z_F },
           "Support must only contain prime ideals of the base ring of O.";
    end if;
    // FIXME/TO DO: Use all primes coprime to Discriminant(A).
    // This requires, that we can handle EichlerOrders of Level p^n locally with pMatrixring ... 
    //  ... we can now handle level p, at least  --SRD
    Primes:= [<p, flat select p else Minimum(p)> : p in Support | Valuation(DA,p) eq 0 and Valuation(DO,p) le 1];
    if strict_support and _Support(DO) subset Support then
      strict_support := false; // it's okay to use all two-sided ideals
    end if;
  end if;
  // Current strict_support setting is final

  actual_support := Primes;  // only used for verbose
  if not strict_support then
    actual_support cat:= [<t[1], flat select t[1] else Minimum(t[1])> : t in FactoredDiscriminant(O)];
  end if;
  vprint Quaternion: "Support to be used is", [t[1] : t in actual_support];
  vprint Quaternion: "These primes lie above", [t[2] : t in actual_support];

  if not flat then 
    NCl, NClh:= NarrowClassGroup(Z_F);
    vprint Quaternion: "The narrow class group of the base field is", grpab_to_string(NCl); 
    if #NCl gt 1 and IsVerbose("Quaternion") then
      printf "Narrow classes of primes in the support are:"; 
      for t in actual_support do 
        printf " %o", Eltseq(t[1]@@NClh);
      end for;
      printf "\n";
    end if;

    if not IsEmpty(Support) then
      // Support was specified, so check 
      // (this is not a sufficient but a necessary condition)
      error if NCl ne sub< NCl | [p[1] @@ NClh : p in Primes] cat (strict_support select [] else  
                                 [(f[1]) @@ NClh : f in FactoredDiscriminant(O) | IsOdd(f[2])]) >,
           "The support does not generate the narrow class group";
    end if;

    // Use automorphisms of the field, if possible
    // IMPORTANT: for correctness, must ensure at all stages that the 
    // set of ideal classes found is closed under the action of Auts
    a := F!(A.1^2);
    b := F!(A.2^2);
    assert A.3 eq A.1*A.2;
    AutsF := [m : m in Automorphisms(F) | m(F.1) ne F.1 and m(a) eq a and m(b) eq b];
    Auts := [map< A->A | x:-> A![m(c) : c in Eltseq(A!x)] > : m in AutsF];
    // For now, only use the subgroup of Auts that fix the original order
    inds := [i : i in [1..#Auts] | [m(x) : x in ZBasis(O)] subset O where m is Auts[i]];
    Auts := [Auts[i] : i in inds];
    AutsF := [AutsF[i] : i in inds];
    // Auts must preserve the set of Primes 
    // TO DO: if Support not specified, enlarge Primes so they are stable
    Primes1 := {t[1] : t in Primes};
    inds := [i : i in [1..#Auts] | forall{P: P in Primes1 | 
                                   ideal<Z_F| {x@m : x in Generators(P)}> in Primes1}
                                   where m is AutsF[i]];
    Auts := [Auts[i] : i in inds];
    AutsF := [AutsF[i] : i in inds];
  end if;

  use_Auts := not flat and #Auts gt 0;

  if not flat or strict_support then
    avoid_IsIsometric := true;
  end if;
  // Current avoid_IsIsometric setting is final

  use_thetas := not flat;
  // use theta series of orders to quickly distinguish order classes
  // TO DO: use thetas also over Q, not only FldNum

  use_norm_classes := not flat and #NCl gt 1; // avoid testing IsNarrowlyPrincipal for every Norm(I)/Norm(J)

  use_Jprime := not flat and Degree(F) le 8; 
  // reason: between degree 8 and 10, the lattice stuff starts to dominates, and Jprime makes that worse
  // TO DO: Jprime is bad for memory, should maybe be careful of that?

  if use_Jprime then
    // make JJs coprime to small primes, so the same JJs can be used for small Hecke operators
    bad_primes_for_Jprime := &* Setseq(Seqset( [tup[1] : tup in Primes] cat Support cat PrimesUpTo(20,F) ));
  end if;

  masstotal := Mass(O);

  vprint Quaternion: "Now starting search for ideal classes";
  vprint Quaternion: " -- search will terminate when masstotal =", masstotal;
  if use_Auts then
    vprintf Quaternion: " -- using %o nontrivial field automorphisms\n", #Auts;
  end if;
  if use_Jprime then
    vprint Quaternion: " -- using the J' trick";
  end if;
  if use_thetas then
    vprint Quaternion: " -- using theta series";
  end if;

  // The Unitgroup does not mod out Z_F^* in the "flat" cases. We take care of this here.
  case Type(F):
    when FldRat: correction := 2;
    when FldFunRat: correction := #BaseRing(F)-1;
    else correction := 1;
  end case;

  s:= #FactoredDiscriminant(O);
  Orders:= [O];
  ZBases:= [ZBasis(O)];
  generations:= [0];                 // the number of p-neighbour steps from the original order
  O`graph:= [[Integers()| ]];        // O`graph[i] contains j if the jth order was a neighbour of the ith
  orders_from_Auts := [Integers()| ]; // indices of orders obtained from other orders via Auts

  vprintf Quaternion, 2: "Determining two-sided ideal class group: "; 
  vtime Quaternion, 2: 
  List:= TwoSidedIdealClasses(O : Support:= Support);
  if strict_support then 
    List:= [ I : I in List | _Support(Norm(I)) subset Support ];
  end if;
  assert forall{I : I in List | IsIdentical(LeftOrder(I), O)}; // this assigns I`LeftOrder 
  NumberOfTwoSided:= [#List];
  if use_norm_classes then
    norm_classes:= [Norm(I) @@ NClh : I in List];
    // TO DO: could be much more elaborate 
    //      + the classes of the neighbours could mostly be obtained from eachother
    //      + avoid computing Nnu for each quotient in IsIsomorphicInternal (as in get_tps)
  end if;
  if use_Jprime then
    JJs := [<JJ,b,P> where JJ,b,P is Jprime(I : coprime_to:= bad_primes_for_Jprime) : I in List];
  end if;
  vprint Quaternion, 1: "Determining unit group:"; 
  vtime Quaternion, 1: 
  u:= correction / #UnitGroup(O);
  masses := [<u,#List>];
  massfound:= #List * u;
  assert masstotal ge massfound;
if false and debug and not strict_support and Type(F) ne FldFunRat then 
    cl := flat select 1 else ClassNumber(Z_F);
    forms := flat select GramMatrix(O) else GramMatrices(O: LLL:=true);
    aut := AutomorphismGroup(forms);
    assert massfound eq cl * #NormOneGroup(O) * 2^(1+s) / #aut;
  end if;

  pValuations:= [Valuation(DO, p[1]): p in Primes];

  vprintf Quaternion, 1: "Starting with %o class%o, mass = %o out of %o\n", 
                         #List, #List ne 1 select "es" else "", massfound, masstotal;
  time0 := Cputime();

  num_iso_tests := 0; // only for verbose info
  time_iso_tests := Cputime();

  check_all_subideals := flat or IsOdd(#NCl);

get_full_graph := false;
if get_full_graph then
 check_all_subideals := true;
 use_Auts := false;
end if;

  PrimesChecked:= [ {Integers() | } ];
  i:= 1; // index of current order
  j:= 0; // index of current prime
while (massfound ne masstotal) or 
get_full_graph and exists{s: s in O`graph | #s lt 1+Norm(Primes[1][1])} do
        
      // TO DO: better to take random edges for random [order,prime] pairs.
      // Currently we try all (or many) edges for each [order,prime] pair.
      // (Actually this isn't clear; it would be better in the case where 
      // there are lots of multiple edges between the same two order classes.)

      // run through pairs [order,prime] systematically
      j +:= 1;
      if j gt #Primes then
        j := 1;
        // Choose another order: 
        // explore those with large unit group first, since they will tend to have
        // neighbours with large unit group (these are the hardest classes to find);
        // if these are similar, we prefer orders closer to the original order, 
        // (to keep the powers of primes small).
        // TO DO: keep track of which [neighbour,prime] pairs have been checked for each order
        priorities := [ExtendedReals()| i in orders_from_Auts or #PrimesChecked[i] eq #Primes
                                        select -Infinity() else 1/masses[i][1] - generations[i] 
                                      : i in [1..#Orders]];
        max, i := Max(priorities);
        if max eq -Infinity() then
          if not check_all_subideals then
            vprint Quaternion: "WARNING: heuristic strategy failed in RightIdealClassesAndOrders";
            // Start again and check all subideals for each order and prime
            // (TO DO: this does happen in the following kind of scenario:
            // there are two orders not yet found, one is not a neighbour the current order
            // while the other has very small mass and its only neighbour is the current order.)
            check_all_subideals := true;
            PrimesChecked:= [ {Integers() | }^^#Orders ];
            i := 1;
            j := 0;
            continue;
          else
            error "Something is seriously wrong in RightIdealClassesAndOrders";
          end if;
        end if;
      end if;
      Include(~PrimesChecked[i], j);

      pp:= Primes[j,1];
      p := Primes[j,2];
      vprintf Quaternion, 1: "Trying p-neighbour ideals for prime #%o (over %o) and order #%o\n", j, p, i;
      k, mk := ResidueClassField(pp);
      index:= 1+ &+NumberOfTwoSided[1..i-1];
      OO:= Orders[i];
      ZbasisOO:= ZBases[i];
      genpp:= flat select [ OO ! pp ] else ChangeUniverse(Generators(pp), OO);

      x11, x12, x21, x22:= get_coords(OO, pp);
      BOp:= [OO | x11, x12, x21, x22 ];

      used := []; // points in P^1(k) used so far
      tries := 0; // number of subideals tried since a new class was found
      num_total:= pValuations[j] eq 0 select #k+1 else 2*#k;
      flip:= false; // toggle, used in 2*#k case
      museq:= []; // initialize to avoid error

      for counter := 1 to num_total do  

        if not check_all_subideals then
          // Switch to the next pair (i,j) if it seems likely there won't be more new classes from this pair
          // TO DO: refined mass formula! or else should make sure to jump to a different genus when we switch
          expected := masstotal/(masstotal-massfound); // = expected # of tries to get a new class (assuming Poisson)
          C := 2^Max(1, 4 - (#Orders-i) ); // be careful about switching when there are not many orders left
          if tries gt C*expected then
            vprintf Quaternion: "Switching after trying %o neighbours of order #%o\n", tries, i;
            break counter; 
          end if; 
        end if; 

        tries +:= 1;
        vprintf Quaternion, 2: ".";
        if counter eq num_total then 
          vprintf Quaternion, 2: "\n";
        end if;

        if flip then
          flip:= false;
          mu:= OO!(BOp[3] + museq[1]*BOp[4] + museq[2]*BOp[2]);
        else
          if (#used eq 0) and (pValuations[j] eq 0) then 
            // if pp | DO the current setup below produces the unique integral twosided ideal of norm pp. So skip this.
            used := [[k|0,1]];
            museq := [0,1];
          else 
            repeat x := Random(k); until [1,x] notin used; 
            Append(~used, [1,x]);
            museq := [1,x@@mk];
          end if;
          mu := OO!(museq[1]*BOp[1] + museq[2]*BOp[3]);
          flip:= pValuations[j] ne 0;
        end if;

        I := rideal<OO | Append(genpp, mu) >;
        assert IsMaximal(O) or RightOrder(I) eq OO;		// If this fails, we managed to pick a noninvertible ideal!
        I`RightOrder := OO;					// use same copy of the order for all the I's
        if debug then
          assert Norm(I) eq pp;
        else
          I`Norm := pp;
        end if;
 
        // Check whether the class of I is new i.e. whether its left order is already there
        // This bit has become simpler: always avoid_IsIsometric in the non-flat case
        // (the ideal testing is now highly optimized).
        // TO DO: when (and if) the new IsIsometric is there, see if it's faster.

        if not avoid_IsIsometric then
          LO:= LeftOrder(I);
          for k:= 1 to #Orders do
            try
              LO_is_old:= IsIsomorphic1(Orders[k], LO: FindElement:= false); 
            catch ERR
              error "Isomorphism testing of orders failed. PLEASE, report this example!";
            end try;
            if LO_is_old then 
              Append(~O`graph[i], k);
              continue counter; 
            end if;
          end for;
          vprintf Quaternion, 2: "\n";
          vprintf Quaternion: "New class found after %os\n", Cputime(time_iso_tests);
        end if;

        // now either we are in "avoid_IsIsometric" mode or we found a new order.
        // Anyway, replace I by I*J where J connects O[i] with O.
        assert IsIdentical(I`RightOrder, List[index]`LeftOrder); 
        I:= mult(I, List[index]);

        if avoid_IsIsometric then 
          if use_norm_classes then
            NClI := Norm(I) @@ NClh;
          end if;
          if use_thetas then
            theta := theta_series(LeftOrder(I));
          end if;

          sum:= 1;
          for k in [1..#Orders] do
            range:= [sum..sum+NumberOfTwoSided[k]-1];
            sum +:= NumberOfTwoSided[k];
            if use_thetas and not IsWeaklyZero(theta - theta_series(Orders[k])) then
              continue; // LeftOrder(I) is not in the kth order class
            end if;
            for jj in range do
              if use_norm_classes and NClI ne norm_classes[jj] then
                continue; // I is not in the jj'th ideal class
              end if;
              num_iso_tests +:= 1;
              if use_Jprime then
                // avoid_IsIsometric, not flat
                // Note: the Jprime trick assumes I is a proper ideal of its order
                I_is_old := test_iso(I, List[jj] : JJ:=JJs[jj]);
                if debug then 
                  assert I_is_old eq test_iso(I, List[jj] : JJ:=0);
                end if;
              else
                I_is_old := test_iso(I, List[jj]);
              end if;
              if I_is_old then
                Append(~O`graph[i], k);
                continue counter;
              end if;
            end for; // jj
          end for; // k

          vprintf Quaternion, 2: "\n";
          vprintf Quaternion: "New class found after %os (%o ideal-isomorphism tests)\n", 
                               Cputime(time_iso_tests), num_iso_tests;
          num_iso_tests := 0;
          time_iso_tests := Cputime();
        end if;

        tries := 0; // reset

        // I is a new ideal class, and its left order LO is a new order class.
        // Next get the other LO-O-ideals as T*I where T are 2-sided LO-ideals

        // The Galois conjugates of I are also classes not seen so far,
        // since the set of ideal classes found so far is Galois stable
        // (So it suffices to test them against eachother)
        GalI := [I];
        if use_Auts then
          for tau in Auts do 
            Itau := rideal< O | [x@tau: x in ZBasis(I)] >;
            Itau`RightOrder := O;
            Itau`Norm := ideal< Z_F | {Z_F| x@tau : x in Generators(Norm(I))} >;
            Append(~GalI, Itau);
            if debug then 
              LO:= LeftOrder(I);
              LOtau := Order([A| x@tau : x in ZBasis(LO)]);
              CheckOrder(LOtau);
              assert LOtau eq LeftOrder(Itau);
              CheckIdeal(Itau);
            end if;
          end for;
        end if;

        // TO DO: assign more stuff to the conjugates?

        // If 'flat or not use_Auts', GalI = [I] and no iso-testing occurs here
        num_old := #List;
        for g := 1 to #GalI do 
          I := GalI[g];
          // Compare I with the new ideals already listed
          for jj := 1 + num_old to #List do 
            if test_iso(I, List[jj] : JJ:= use_Jprime select JJs[jj] else 0) then
              continue g; // the ideal class of I was already listed
            end if;
          end for;
          if g gt 1 then
            vprint Quaternion: "Obtained a new class from Galois action";
          end if;
          LO := LeftOrder(I); // could compute LO using Galois action

          vprint Quaternion, 2: "Determining two-sided ideal class group:"; 
          vtime Quaternion, 2: 
          T:= TwoSidedIdealClasses(LO : Support:= Support);
          if strict_support then
            T:= [ t : t in T | _Support(Norm(t)) subset Support ];
          end if;
          vprint Quaternion, 1: "Determining unit group:"; 
          vtime Quaternion, 1: 
          u:= correction / #UnitGroup(LO);
if false and debug and not strict_support and Type(F) ne FldFunRat then 
            cl := flat select 1 else ClassNumber(Z_F);
            forms := flat select GramMatrix(O) else GramMatrices(O: LLL:=true);
            aut := AutomorphismGroup(forms);
            assert #T*u eq cl * #NormOneGroup(O) * 2^(1+s) / #aut;
          end if;
          massfound +:= #T*u;
          Append(~masses, <u,#T>);
          Append(~ZBases, ZBasis(LO));
          Append(~NumberOfTwoSided, #T);
          Append(~Orders, LO);
          Append(~generations, 1+generations[i]);
          Append(~PrimesChecked, {Integers()| });
          if g gt 1 then
            Append(~orders_from_Auts, #Orders);
          end if;
          Append(~O`graph[i], #Orders);
          Append(~O`graph, [Integers()| ]);

          for t in T do
            tI:= mult(t, I);
            tI`RightOrder:= O;
            tI`LeftOrder:= LO;
            if debug then assert forall{l : l in List | not test_iso(l, tI) }; end if;
            Append(~List, tI);
            if use_norm_classes then
              Append(~norm_classes, Norm(tI) @@ NClh);
            end if;
            if use_Jprime then
              Append(~JJs, <JJ,b,P> where JJ,b,P is Jprime(tI : coprime_to:= bad_primes_for_Jprime));
            end if;
          end for;

        end for; // g

        vprintf Quaternion, 1: "Now found %o ideal classes, with mass %o out of %o (%o%%)\n", 
                               #List, massfound, masstotal, 
                               RealField(Floor(Log(10,1+pc))+2)!pc where pc is 100*massfound/masstotal;
        vprintf Quaternion, 2: "Mass contributions for orders so far are \n%o\n", 
                               #masses gt 1000 select Multiset(masses) else  
                               [* t[2] eq 1 select t[1] else t : t in masses *];
        if masstotal eq massfound then 
          vprintf Quaternion, 1: "Finished!  Search for ideal classes took %os\n", Cputime(time0);
if not get_full_graph then
          break; 
end if;
        end if;
        error if (masstotal lt massfound), "Found too many RightIdealClasses!";
        if debug and not flat then
          // The ModFrmHil code assumes that the left orders are identical iff they are equal 
          assert &and[ exists{Ord: Ord in Orders | IsIdentical(JJ`LeftOrder, Ord)} : JJ in List ]; 
        end if;
      end for; // counter

  end while; // massfound ne masstotal

  if use_thetas then
    vprint Quaternion, 2: "Theta series of the left orders (sorted):", 
                              Sort([theta_series(OO) : OO in Orders]);
  end if;

  if (masstotal ne massfound) then
    assert not IsEmpty(Support);
    // really, this should never ever happen
    error "The given support was not large enough to enumerate all classes!";
  end if;

  if compute_order_classes and strict_support then
    vprint Quaternion, 1: "Support did not contain the divisors of the discriminant!",
                          "\nNow determining conjugacy classes of orders";
    cc_time0 := Cputime();
    sum:= 1;
    Conn:= [];
    for i:= 1 to #Orders do
      Append(~Conn, List[sum]);
      sum +:= NumberOfTwoSided[i];
    end for;
    i:= 1;
    while i le #Orders do
      T:= TwoSidedIdealClasses(Orders[i]);	// is cached anyway
      I:= Conjugate(Conn[i]);
      for j in [#Orders..i+1 by -1] do
        _, IJ:= Conn[j] * I;			// do not call mult here! 
        if exists{t : t in T | test_iso(IJ, t) } then
          NumberOfTwoSided[i]+:= NumberOfTwoSided[j];
          Remove(~Orders, j);
          Remove(~NumberOfTwoSided, j);
          Remove(~Conn, j);
          if NumberOfTwoSided[i] eq #T then break; end if;
        end if;
      end for;
      assert(NumberOfTwoSided[i] eq #T);
      i+:= 1;
    end while; 
    vprint Quaternion, 1: "Time for conjugacy classes of orders:", Cputime(cc_time0);

  elif not compute_order_classes and strict_support then
    // we have not computed the conjugacy classes, so don't cache the Orders
    Orders:= [Universe(Orders)| ];
  end if;

  if not flat and #NCl gt 1 then
    // Sort ideals according to the narrow ideal class of their norms
    // DO NOT CHANGE this -- Hilbert modular forms rely on it
    norm_classes := [Eltseq(Norm(I) @@ NClh) : I in List];
    ParallelSort(~norm_classes, ~List);
  end if;

  // Cache results, using minimal Support
  Support := Setseq(&join[ _Support(Norm(I)) : I in List ]);
  if not assigned O`RightIdealClasses then 
    O`RightIdealClasses := [* *]; 
  end if;
  rec := rec< rids_record | rids := List, support := Support >;
  if not IsEmpty(Orders) then 
    rec`orders := Orders;
  end if;
  Append(~O`RightIdealClasses, rec);

  return List, Orders; 
end function;


/*
* from Algebra/AlgQuat/ramified.m
*/
//-------------
//
// Algorithms for real places.
//
//-------------

// Stupid map, maps {-1,1} -> {1,0}
function h(x);
  if x eq -1 then
    return GF(2) ! 1;
  elif x eq 1 or x eq 0 then
    return GF(2) ! 0;
  else
    print x;
    error "Bad h!";
  end if;
end function;

// Returns the sequence of signs of the real embeddings of s.
function RealValuations(V, s);
  F := Parent(s);
  if not ISA(Type(F), FldNum) then
    F := NumberField(Parent(s));
    s := F ! s;
  end if;
  return [ h(Sign(Evaluate(s,v))) : v in V];  
end function;

/********** from Algebra/AlgQuat/enumerate.m **************/

//-------------
//
// Reduced bases.
//
//-------------

// Requires the base field to be totally real; reduces the coefficients
// with respect to the standard basis of A.

function ReducedBasisInternal(P, A : return_new_basis:=true, q0 := 0, w := []); 
  if Type(P) eq SeqEnum then
    Pbasis := P;
  else
    if BaseField(A) cmpeq Rationals() then
      Pbasis := ZBasis(P);
    else
      Pbasis := ZBasis(P, A);
    end if;
  end if;
  m := #Pbasis;

  if IsDefinite(A) then
    //Pbmat := Matrix([ &cat [Flat(a) : a in Eltseq(b)] : b in Pbasis ]);
    Pbmat := Matrix([ Flat(b) : b in Pbasis ]);
    M := 1/2 * Pbmat * TraceFormsOnQBasis(A) * Transpose(Pbmat);
    /* Obvious but slow way, because mult for matrices over FldNum is slow
    // GramMatrixofAlgebra gives the norm form A x A -> BaseField(A)
    Pbmat := Matrix([ Eltseq(b) : b in Pbasis ]); 
    PbasisGram := Pbmat * GramMatrixofAlgebra(A) * Transpose(Pbmat);
    Mold := 1/2 * Matrix( Rationals(), m, [ Trace(x): x in Eltseq(PbasisGram)]);
    assert Mold eq M; */

    L, T := LLL(LatticeWithGram(M : CheckPositive:=debug));
  elif IsTotallyReal(BaseField(A)) then
    if BaseField(A) cmpeq Rationals() then
      S := [];
    else
      _, S := Discriminant(A);
    end if;
    if #S eq Degree(BaseField(A))-1 then
      prec0 := 20*Degree(BaseField(A));
      prec := prec0;
      while true do 
        if q0 cmpeq 0 then
          // don't set this as the default because then it gets executed in all cases
          q0 := UnitDisc(:Precision := prec)!0; 
        elif Parent(q0)`prec lt prec then
          q0 := UnitDisc(:Precision := prec)!ComplexValue(q0);           
        end if;
        M := DefiniteGramMatrix(Pbasis : q := q0, w := w);
        try
          b := IsPositiveDefinite(M);
        catch e
          assert "efinite" in e`Object;  // "cannot determine definiteness"
          b := false;
        end try;
        if b then
          break;
        end if;
        prec +:= prec0;
        vprintf Quaternion: "QuaternionAlgebra: increasing precision to %o\n", prec;
      end while;
      L, T := LLL(LatticeWithGram(M));
      // TO DO: do we still get 'not positive definite' errors from LatticeWithGram ?
    else
      Foo := RealPlaces(BaseField(A));

      M := Matrix([[Evaluate(Pb[i],v) : i in [1..4], v in Foo] : Pb in Pbasis]);
      L, T := LLL(LatticeWithBasis(M));
    end if;
  else
    T := IdentityMatrix(BaseField(A), m);
    L := StandardLattice(m);
  end if;

  underlyingPbasis := Pbasis;
  if return_new_basis or debug then 
    Pbasis := [ &+[Pbasis[j]*T[i,j] : j in [1..m]] : i in [1..m]];
  end if;

  if debug and IsDefinite(A) then
    assert &and[ Trace(Norm(Pbasis[i])) eq Norm(L.i) : i in [1..m]];
    assert [Trace(Norm(x+y)-Norm(x)-Norm(y))/2 : x,y in Pbasis]
           eq Eltseq(GramMatrix(L));
    assert [Trace(Norm(x+y)-Norm(x)-Norm(y))/2 : x,y in underlyingPbasis]
           eq Eltseq(InnerProductMatrix(L));  // tautology 
  end if;
  
  if return_new_basis then 
    return Pbasis, L, underlyingPbasis;
  else 
    return L, underlyingPbasis; 
  end if;
end function;


/***********************************
* from Algebra/AlgAss/ideals-jv.m
************************************/

// Data can be stored on AlgAssVOrdIdl's by attaching a record of this format
// as I`PackageAttributes (the type does not support package attributes directly)

AlgAssVOrdIdlData := recformat< 
   Jprimes:List               // list of tuples <JJ,b,n> containing output of Jprime
                         >;

function TotallyPositiveUnits(Z_F)
  if assigned Z_F`TotallyPositiveUnits then 
    return Z_F`TotallyPositiveUnits; 
  end if;

  UF, mUF := UnitGroup(Z_F);
  M := [[(1-t) div 2 : t in RealSigns(mUF(UF.i))] : i in [1..#Generators(UF)]];
  hk := hom<UF -> AbelianGroup([2 : ind in [1..Degree(Z_F)]]) | M>;
  UFplus := sub<UF | Kernel(hk)>;
  UFplusmodsq,msq := quo<UFplus | [2*UF.i : i in [1..#Generators(UF)]]>;
  Z_F`TotallyPositiveUnits := [mUF(u@@msq) : u in UFplusmodsq];
  return Z_F`TotallyPositiveUnits;
end function;

// Given a sequence of right ideal class reps, compute a sequence
// of equivalent reps with norms supported in the given primes
// (which must be disjoint from the support of the rids1).
// Also return sequence of algebra elts such that rids[i] = elts[i]*rids1[i]

// TO DO: could convert other stuff too, eg the left orders and unit groups

function convert_rids(rids1, primes)

  assert not IsEmpty(rids1);
  if debug then
    assert not &and [t[1] in primes : t in Factorization(Norm(I)), I in rids1];
  end if;

  O := Order(rids1[1]);
  ZF := BaseRing(O);
  F := NumberField(ZF);
  PI := PowerIdeal(FieldOfFractions(ZF));
  tot_pos_units := TotallyPositiveUnits(ZF);

  NCl, cl := NarrowClassGroup(F);
  S := AbelianGroup([0 : p in primes]);
  StoNCl := hom< S -> NCl | [p @@ cl : p in primes] >;

  // Lattice of principal ideals within S
  K := Kernel(StoNCl);
  L := LatticeWithBasis(Matrix(Integers(), [Eltseq(S!K.i) : i in [1..Ngens(K)]] ));
  Lgens := [ZF| ];
  for v in Basis(L) do 
    I := &* [primes[i]^v[i] : i in [1..#primes]];
    bl, g := IsNarrowlyPrincipal(I); assert bl;
    Append(~Lgens, g);
  end for;

  procedure select_vecs(~vecs, v1)
    vecs := [v : v in vecs | forall{c : c in Eltseq(v+v1) | c ge 0}];
    vecs_norms := [Integers()| &*[Norm(primes[i])^vv[i] : i in [1..#primes]]
                                 where vv is v+v1 
                             : v in vecs ];
    ParallelSort(~vecs_norms, ~vecs);
  end procedure;

  U := Universe(rids1);
  rids := [U| ];
  elts := [Algebra(Ring(U))| ];
  vprintf Quaternion: "Converting right ideal class representatives to support \n%o\nwith norms %o\n", 
                      primes, [Norm(p) : p in primes];
  time0 := Cputime();
  IndentPush();
  for I1 in rids1 do 
    // Want I = x*I1 with Norm(I) = N, so find x in I1^-1 with Norm(x) = u*s 
    // where s runs over generators of principal ideals supported within primes,
    // and u runs over units
    I1inv := ZBasis(LeftInverse(I1));
    N1 := Norm(I1);
    bl, n := HasPreimage(N1 @@ cl, StoNCl);
    error if not bl, 
         "The given primes do not generate the narrow ideal classes of the norms";
    e := Eltseq(n); 
    N := &* [PI| primes[i]^e[i] : i in [1..#primes]];
    bl, s1 := IsNarrowlyPrincipal(N/N1); assert bl;
    v1 := Vector([Valuation(s1,p) : p in primes]);
    // Test candidates s in same coset as s1, integral at primes, with small Norm
    // TO DO: can we guess an s that works? or how large s is needed to find I1?
    // TO DO: run through candidates s strictly in order of Norm 
    // (currently, we get them in order of L2-norm of exponent vectors,
    // in batches and then reorder each batch by Norm)
    _, i := ClosestVectors(L, -v1);
    i +:= 4;
    vecs := [tup[1] : tup in CloseVectors(L, -v1, i)];
    select_vecs(~vecs, v1);
    vprintf Quaternion, 2: "%o : ", Norm(N1);
    vtime Quaternion, 2:
    while true do 
      for v in vecs do 
        c := Coordinates(v); // coords wrt basis of L
        s := s1 * &* [Lgens[i]^c[i] : i in [1..#primes]];
        vprintf Quaternion, 2: "%o ", Numerator(Abs(Norm(s)));
        for u in tot_pos_units do
          bl, x := has_element_of_norm(I1inv, u*s : prune:=false);
          if bl then
            I := x*I1;
            Append(~rids, I);
            Append(~elts, x);
            continue I1;
          end if;
        end for;
      end for; // v in vecs
      i +:= 1;
      vecs := [tup[1] : tup in CloseVectors(L, -v1, i, i)];
      select_vecs(~vecs, v1);
    end while;
  end for; // I1

IndentPop();
  vprintf Quaternion: "Converting right ideal representatives took %os\n", Cputime(time0);

  assert #rids eq #rids1;

  // actual support of rids
  support := {PI| };
  for I in rids do 
    NI := Norm(I);
    support join:= {P : P in primes | Valuation(NI, P) ne 0};
    if #support eq #primes then 
      break;
    end if;
  end for;

  if debug then
    assert &and [t[1] in primes : t in Factorization(Norm(I)), I in rids];
    assert &and [rids[i] eq elts[i]*rids1[i] : i in [1..#rids]];
  end if;

  // Cache
  Append(~O`RightIdealClasses, 
     rec< rids_record | rids := rids, rids1 := rids1, rids_conversion := elts, 
                        support := Sort(Setseq(support)) > );

  return rids, elts;
end function;

// This is a helper for ideal-isomorphism testing for definite orders.
// Given an invertible right O-ideal J, returns b in J and JJ s.t O*b = J*JJ (with b small) 
// and with JJ of prime power norm, coprime to the given integral ideal of BaseRing(O)

function Jprime(J : coprime_to:=1) 
  // Check cache
  if assigned J`PackageAttributes and assigned J`PackageAttributes`Jprimes then
    for tup in J`PackageAttributes`Jprimes do 
      JJ, b, normb := Explode(tup); 
      NJJ := Norm(JJ); 
      if coprime_to cmpeq 1 or AbsoluteNorm(NJJ + ideal< Order(NJJ) | coprime_to >) eq 1 then 
        return JJ, b, normb; 
      end if; 
    end for; 
  end if;

  O := Order(J);
  assert IsRightIdeal(J) and O eq RightOrder(J); 
  OJ := LeftOrder(J);
  A := Algebra(O);
  K := BaseField(A);
  // set up usual pos def Tr(N(.)) on J
  ZBJ := ZBasis(J);
  L := ReducedBasisInternal(ZBJ, A : return_new_basis:=false);
  
  // iterate small combinations of the reduced basis, until we find b with Nb/NJ okay
  m := Integers()! Norm(coprime_to);
  NJ := Norm(Norm(J));
  Lmat := BasisMatrix(L);
  SVPB := 1; SVP := ShortVectorsProcess(StandardLattice(Dimension(L)), SVPB); 
  repeat 
    sv, nsv := NextVector(SVP);
    if nsv eq -1 then
      SVPB *:= 2; SVP := ShortVectorsProcess(StandardLattice(Dimension(L)), SVPB);
      continue; end if;
    v := Vector( ChangeRing(sv, BaseRing(Lmat)) * Lmat );
    b := &+[A| v[i]*ZBJ[i] : i in [1..#ZBJ] ];
    nn := Integers()! (Norm(Norm(b))/NJ); 
  until GCD(nn,m) eq 1 and #PrimeDivisors(nn) eq 1;
  
  // get pseudomatrix for OJ*b with minimal work:
  CIs_OJ := CoefficientIdeals(PseudoMatrix(OJ));
  bas_OJ := Basis(OJ);  assert Universe(bas_OJ) eq A;
  POJb := PseudoMatrix( CIs_OJ, Matrix([Eltseq(x*b) : x in bas_OJ]) );
  JJ := ColonInternal(POJb, PseudoMatrix(J,A), A, false); // 'false' means right multipliers 
  Obasismat := Matrix([Eltseq(A!x) : x in Basis(O)]);
  JJmat,kn := Solution(Obasismat, ChangeRing(Matrix(JJ),K)); // change basis from A to O
  JJ := PseudoMatrix( CoefficientIdeals(JJ), JJmat );
  JJ := lideal< O | JJ : Check:=debug >;
  if debug then 
    assert OJ eq Order(bas_OJ, CIs_OJ);
    assert lideal< OJ | ZBasis(POJb,A) > eq OJ*b;
    assert RightOrder(JJ) eq OJ^b; // or is it b^-1 ??
    assert J*JJ eq OJ*b; 
  end if;

  normb := ideal<BaseRing(O)|Norm(b)>;
  JJ`Norm := normb/Norm(J);
  
  // Cache JJ
  if not assigned J`PackageAttributes then 
    J`PackageAttributes := rec< AlgAssVOrdIdlData | >; end if;
  if not assigned J`PackageAttributes`Jprimes then 
    J`PackageAttributes`Jprimes := [* *]; end if;
  Append(~J`PackageAttributes`Jprimes, <JJ, b, normb>);

  return JJ, b, normb;
end function;

function IsPrincipalZBasis(zbasis, Nnu) 
  // It suffices to look for nu with Norm(nu) = u*Nnu for some u in a finite list 
  // of representatives for the totally positive units modulo squares of units.
  for u in TotallyPositiveUnits( Integers(BaseRing(Universe(zbasis))) ) do
    vprintf Quaternion,3: "IsIsomorphic: enumerating with unit %o\n", u; 
    bool, nu := has_element_of_norm(zbasis, u*Nnu); 
    if bool then return true, nu; end if;
  end for;
  return false, _;
end function;

function IsIsomorphicInternal(I,J : real_places:=0, UnitRealValuations:=<>, JJ:=0 )        
  vprintf Quaternion,3: "Calling IsIsomorphic for ideals of norms %o,%o\n", Norm(Norm(I)), Norm(Norm(J));
  if debug then CheckIdeal(I); CheckIdeal(J); end if;

  O := Order(I);
  A := Algebra(O);
  F := BaseField(A); 
  Z_F := BaseRing(O);
  FeqQ := F cmpeq Rationals();

  // We need to determine whether there exists an element nu in JcolonI 
  // with Norm(nu) * Norm(I) = Norm(J).  Nnu stands for Norm(nu) below.
  N := Norm(J)/Norm(I);
  if IsDefinite(A) then 
    bl, Nnu := IsNarrowlyPrincipal(N : real_places:=real_places, UnitRealValuations:=UnitRealValuations);
  else  
    if FeqQ then
      bl := true;
      Nnu := N;
    else
      bl, Nnu := IsPrincipal(N); 
    end if;
  end if;
  if not bl then
    return false, _;  // necessary, but not sufficient condition
  end if;

  if IsDefinite(A) then
    // This is a way of avoiding the (somewhat painful) colon operation!
    // Suppose b generates J*JJ.  Then I*JJ = I*J^-1*b, 
    // so x generates I*JJ <==> x/b generates I*J^-1
    if JJ cmpne 0 then
      JJ, b := Explode(JJ);
      if debug then 
        assert LeftOrder(J)*b eq J*JJ; 
        assert Norm(JJ) + Norm(I) eq 1*Z_F; 
      end if; 
      // By coprimality, I*JJ = I meet JJ, which we compute as a Z-module
      IJJ_ZB := IntersectionZBasis(I, JJ);
      bool, x := IsPrincipalZBasis( IJJ_ZB, Norm(b)/Nnu ); 
      if bool then 
        if debug then assert J cmpeq (b/x)*I or J cmpeq I*(b/x); end if;
        return true, b/x;
      else 
        return false, _;
      end if;
    end if;        

    // [J:I] = J*I^-1 for right ideals, or I^-1*J for left ideals, as a pmatrix
    // The fourth argument means take left multipliers when true
    JcolonI := ColonInternal(PseudoMatrix(J, A), PseudoMatrix(I, A), A, IsRightIdeal(I) and IsRightIdeal(J)
                            : Hermite:=false); // empirically, saves time to skip the final Hermite
    JcolonI_ZB := ZBasis(JcolonI, A);
    bool, nu := IsPrincipalZBasis(JcolonI_ZB, Nnu);
    if bool then 
      if debug then assert J cmpeq nu*I or J cmpeq I*nu; end if; 
      return true, nu;
    else 
      return false, _;
    end if;
  else
    // The quaternion algebra A satisfies the Eichler condition, so 
    // there the norm map gives a bijection of sets from the set
    // of ideal classes to Cl^S(F), where S is the set of ramified 
    // infinite places of A.
    _, S := RamifiedPlaces(A);
    if not FeqQ then
      if real_places cmpeq 0 then real_places := RealPlaces(F); end if;
      sgnsNnu := RealSigns(Nnu : real_places:=real_places);
      sgns := [sgnsNnu[Index(real_places, v)] : v in S];
      u := RealWeakApproximation(S, sgns : UnitOnly, UnitRealValuations:=UnitRealValuations);
      if u cmpeq false then
        return false, _;
      end if;
    end if;
    // Otherwise, u*Nnu is now a generator for the ideal Norm(I)/Norm(J)
    // with the right signs, so by Eichler's theorem, I is isomorphic to J.
    JcolonI := Colon(J, I);
    Lbasis, L := ReducedBasisInternal(JcolonI, A);  

  //"Old way ..."; time
  //delta := EnumerativeSearchUntilSuccess(Lbasis, Abs(Norm(Nnu)));

    d := Degree(F);
    NNnu := Abs(Norm(Nnu));
    m := 0;
    SVP := ShortVectorsProcess(L, d);
    while true do
      v := NextVector(SVP);
      if IsZero(v) then
        m +:= 1;
        SVP := ShortVectorsProcess(L, m*d, (m+1)*d);
        continue;
      end if;
      // Coordinates often fails, due to even slight precision loss.
      // Don't want to break it now, so just putting potentially infinite loop
      // in already-broken cases
      // SRD, Dec 2011
      try
        coords := Coordinates(v);
        delta := &+[coords[i]*Lbasis[i] : i in [1..4*d]];
        okay := true;
      catch ERROR
        okay := false;
      end try;
      if not okay then
        continue; // even though likely to never by okay
      end if;
      // In the case where ReducedBasisInternal constructs a LatticeWithGram,
      // we could avoid Coordinates: if JcolonI_ZB is the same ZBasis(JcolonI) then
      // delta := &+[Round(v[i])*JcolonI_ZB[i] : i in [1..4*d]];
      if Abs(Norm(Norm(delta))) eq NNnu then
        return true, delta;
      end if;
    end while;
  end if;
end function;


// If PI, PJ are pseudomatrices with respect to the algebra A, 
// representing lattices I, J, compute the colon
//   (I:J) = {x in A : x*J in I} 
// (if isLeft, otherwise swap).  Returns a pseudomatrix.

function ColonInternal(PI, PJ, A, isLeft : Hermite:=true);
  CI := CoefficientIdeals(PI);
  CJ := CoefficientIdeals(PJ);
  Si := Matrix(PI)^(-1);

  n := Nrows(Si);

  F := BaseField(A);
  M := Matrix(F,0,n, []);
  C := [];
  BJ := Matrix(PJ);
  for i in [1..n] do
    b := A!BJ[i];
    if isLeft then
      m := Transpose(RepresentationMatrix(b : Side := "Right")*Si);
    else
      m := Transpose(RepresentationMatrix(b : Side := "Left")*Si);
    end if;
    M := VerticalJoin(M, m);
    C cat:= [CJ[i]/c : c in CI];
  end for;

  P := HermiteForm(PseudoMatrix(C, M));
  C := CoefficientIdeals(P);
  M := Transpose(Matrix(P))^(-1);

  P := PseudoMatrix([C[i]^(-1) : i in [1..n]], M);
  if Hermite then P := HermiteForm(P); end if;
  return P;
end function;

// Find some or all nu in the module generated by ZB (inside a quat alg) 
// such that Norm(nu) = Nnu

function has_element_of_norm(ZB, Nnu : all:=false, svp:=true, prune:=false)

  A := Universe(ZB);  
  F := BaseRing(A);  
  Z_F := Integers(F);
  Nnu:= F ! Nnu;

  // The trick here ensures we are looking for vectors of the twisted trace form
  //     Tr( 1/Nnu * trd(x*y^bar) )
  // having length 2*[F:Q]. These are shortest vectors if nu generates the norm.
  // Here the mat mults are a bit costly when field degree is 2

  M    := Matrix(4*Degree(F), &cat [Flat(x) : x in ZB]);
  R    := RepresentationMatrix(1/Nnu);
  Gram := M * DiagonalJoin([R : i in [1..4]]) * TraceFormsOnQBasis(A) * Transpose(M);
  Gram, d:= IntegralMatrix(Gram);
  c    := Content(Gram);
  if c ne 1 then Gram := Gram div c; end if;
  B    := 2 * AbsoluteDegree(F) * d/c;
  
  if not IsIntegral(B) then
    return false, _;
  end if;

  // Strongest available LLL!  
  // TO DO: BKZ when that's available for lattices defined by Gram matrices
  L := LatticeWithGram(Gram : CheckPositive:=debug);
  L := LLL(L : Delta:=0.9999, Eta:=0.5001, DeepInsertions:=(Dimension(L) le 80), Proof:=false);

  // Empirical observation: when the answer consists of 1 or 0 elements,
  // typically this is also the number of candidate short vectors.
  // When the answer contains many elements, the number of candidates 
  // is sometimes still the same, but usually considerably larger.

  // TO DO: When there are many short vectors, we'd like to use ShortVectorsProcess,
  // but it uses Allan's old enumeration; ShortVectors using Damien's enumeration 
  // saves some time, but obviously takes memory.

  if all or not svp or prune then 

    if prune then
      d := Dimension(L);
      linear := [RealField()| 1 - i/d : i in [0..d-1]];
      SV := ShortVectors(L, B, B : Prune:=linear);
    else
      SV := ShortVectors(L, B, B);
    end if;

    if all then 
      elts := Internal_has_element_of_norm(SV, ZB, Nnu, F!1);
    else
      for tup in SV do 
        s := tup[1];
        anu := AddMult(s, ZB);
        if Norm(anu) eq Nnu then   // J = product of (nu) and I
          return true, anu;
        end if;
      end for;
    end if; // all

    // #SV, "candidates"; #elts, "elements";

  else

    SVP := ShortVectorsProcess(L, B, B);
    s,l := NextVector(SVP);

    if all then // (not reachable, currently)
      elts := [A| ];
      while l ne -1 do
        anu := AddMult(s, ZB);
        if Norm(anu) eq Nnu then   // J = product of (nu) and I
          Append(~elts, anu);
        end if;
        s,l := NextVector(SVP);
      end while;
    else
      while l ne -1 do
        anu := AddMult(s, ZB);
        if Norm(anu) eq Nnu then   // J = product of (nu) and I
          return true, anu;
        end if;
        s,l := NextVector(SVP);
      end while;
    end if; // all

  end if;

  if all and #elts gt 0 then 
    return true, elts;
  else 
    return false, _; 
  end if;
end function;

/*********************************************
* From Geometry/BianchiNew/defs.m
**********************************************/

HomologyRec:=recformat<
    zero_sharbly_space,//
    H,//homology as a quotient
    ToH,//map to quotient H
    coefficient_ring,// coeff ring of homology
    relations,//boundary relations
    cycles
    >;

OrbitRec:=recformat<
    rStab,//stabilizer subgroup image in GL_2(rF)
    entry,//a list giving the total order number of
    //each Gamma0 class to know where to put the entry
    //in the matrix for the boundary
    orbit_type, //line orbits
    total_number, //number of this type of orbit
    gamma_list,//This is a list of gamma in Gamma_0, such that
    //[0:1]*gamma = a0, where a0 is the first point in each orbit.
    //It is used to pick a representative of the polytope when
    //we compute homology.
    orbit_mover_list,
    //this is a list of g in Stab(cell) such that a sends the point
    //a to a0 in its orbit.  It is given in the order from
    //projective_list.
    orbit_number_list,
    //This is a list of +/- 1 that tells if a in orbit agrees or
    //disagrees with orientation of a0
    non_orientable_orbits //a sequence of the non-orientable orbits indices
	>;

/*********************************************
* From Geometry/BianchiNew/setlevel.m
**********************************************/

function gamma_list(LO,proj,level)
    //Computes gamma_list;
    O:=Parent(proj[1,1]);
    gammalist:=[ ];
    //these take [0:1] to a0.  Given as a list, one for each Gamma0 type;
    for Gamma0type in [1..Maximum(LO)] do
	ind:=Position(LO, Gamma0type); //Is this guaranteed to be the first
	//occurence of Gamma0type in LO?
	//ind:=Minimum([i:i in [1..#LO]|LO[i] eq Gamma0type]);
	olda:=proj[ind];
	a:=olda;
	id := ideal<O|a[1],a[2]>;
	while id ne 1*O do
	    n := Random(Basis(level));
	    a:=[a[1]+n,a[2]];
	    id := ideal<O|a[1],a[2]>;
	end while;
	if a[1] eq 0 then
	    gamma:=Matrix([[O|1,0],[O|0,1]]);
	elif a[1] eq 1 then
	    gamma:=Matrix([[O|0,-1],[O|1,a[2]]]);
	else
	    I:=ideal<O|a[1]>;
	    J:=ideal<O|a[2]>;
	    tf,i,j:=Idempotents(I,J);
	    assert tf;
	    s:=O!(i/a[1]);
	    t:=O!(j/a[2]);
	    gamma:=Matrix([[O|t,-s],[O|a[1],a[2]]]);
	end if;
	gammalist[Gamma0type]:=gamma;
    end for;
    return gammalist;
end function;

function orbit_number_list(OT,F,cell,proj,proj_map)
    onumber:=[];
    OF := Integers(F);
    stabplus := [Matrix(OF,A) : A in cell`stabilizer_plus];
    for otype in [1..Maximum(OT)] do
	ind:=[i:i in [1..#proj]|OT[i] eq otype];
	a0:=proj[ind[1]];
	for i in ind do
	    b:=proj[i];
	    tf:=exists(g){g: g in stabplus | rep eq a0 
		             where _,rep:=proj_map(b*g,false,false)};
	    if tf then
		onumber[i]:=1;
	    else onumber[i]:=-1;
	    end if;
	end for;
	assert onumber[ind[1]] eq 1;
    end for;
    return onumber;
end function;

function non_orientable_orbits(OT,F,cell,proj,proj_map)
    no:=[];
    OF := Integers(F);
    stabplus := [Matrix(OF,A) : A in cell`stabilizer_plus];
    stab := [Matrix(OF,A) : A in cell`stabilizer];
    for otype in [1..Maximum(OT)] do
	ind:=[i:i in [1..#proj]|OT[i] eq otype];
	b:=proj[ind[1]];
	S:=[g:g in stab | g notin stabplus ];
	tf:=exists(g){g: g in S| rep eq b
		         where _,rep:=proj_map(b*g,false,false)};
	if tf then Append(~no,otype); end if;
    end for;
    return no;
end function;

function brm(M,g)
    O:=Integers(BaseField(M));
    proj:=M`LevelData`projective_space;
    proj_map:=M`LevelData`projective_space_map;
    v:=[O | g[2,1],g[2,2]];
    _,nv:=proj_map(v,false,false);
    ans:=Position(proj,nv);
    return ans;
end function;

function GetOrbits(M,polydim)
    vprintf Bianchi,2:"Computing %o-dimensional cell orbits.\n",polydim;
    F:=BaseField(M);
    OF := Integers(F);
    levelrec:=M`LevelData;
    total:=[];
    level:=Level(M);
    if polydim eq 3 then
	std:=M`ModFrmData`three_poly;
    elif
	polydim eq 2 then
	std:=M`ModFrmData`two_poly;
    elif
	polydim eq 1 then
	std:=M`ModFrmData`one_poly;
    end if;
    proj:=levelrec`projective_space;
    proj_map:=levelrec`projective_space_map;
    rF:=levelrec`rF;
    base:=0;
    for cell in std do
	Stab:=[Matrix(OF,A) : A in cell`stabilizer];
	orbitrec:=rec<OrbitRec|>;
	orbitrec`orbit_type:=ProjectiveLineOrbits(Stab,proj,proj_map);
	orbitrec`total_number:=Maximum(orbitrec`orbit_type);
	orbitrec`gamma_list:=gamma_list(orbitrec`orbit_type,proj,level);
	assert &and[brm(M,g[i]) eq Position(orbitrec`orbit_type,i)
	    where g:=orbitrec`gamma_list:i in [1.. #orbitrec`gamma_list]];
	orbitrec`orbit_number_list:=
	    orbit_number_list(orbitrec`orbit_type,F,cell,proj,proj_map);
	orbitrec`non_orientable_orbits:=
	    non_orientable_orbits(orbitrec`orbit_type,F,cell,proj,proj_map);
	orbitrec`entry:=[base+i:i in [1..orbitrec`total_number]];
	Append(~total,orbitrec);
	base:=base+orbitrec`total_number;
    end for;
    vprintf Bianchi,2:"  Found %o Gamma0-orbits of cells.\n",
	&+[a`total_number:a in total];
    return total;
end function;

procedure SetLevel(M)
    //Given F and level, attaches ModFrmData M`LevelDataord.
    //Assumes F has been set up and cells have been computed.}
    level:=Level(M);
    if not assigned M`LevelData`projective_space then 
	F:=BaseField(M);
	O:=Integers(F);
	rF:=quo<O|level>;
	M`LevelData`rF:=rF;
	M`LevelData`good_a:=AssociativeArray();
	M`LevelData`projective_space, M`LevelData`projective_space_map:=
            ProjectiveLine(rF:Type:="Vector");
    end if;
    
    if not assigned M`LevelData`two_orbits then 
	M`LevelData`two_orbits:=GetOrbits(M,2);
	M`LevelData`one_orbits:=GetOrbits(M,1);
	M`LevelData`total_number_of_one_orbits:=
	    &+[a`total_number:a in M`LevelData`one_orbits];
	M`LevelData`total_number_of_two_orbits:=
	    &+[a`total_number:a in M`LevelData`two_orbits];
	M`LevelData`homology:=rec<HomologyRec|>;
    end if;
end procedure;

/*********************************************
* From Geometry/BianchiNew/cohomology.m
**********************************************/

function get_column(M,GLtype2,Gamma0type2);
    //returns the column in the boundary matrix associated to the GLtype
    //and Gamma0type.  Does not throw out non-orientable sharblies.
    //Just adds them to the relations.
    GLstd2:=M`ModFrmData`two_poly[GLtype2];
    orbits2:=M`LevelData`two_orbits[GLtype2];
    gamma0:=orbits2`gamma_list[Gamma0type2];
    boundary:=[ L : L in GLstd2`GL_facet_types | L[1] ne 0 ];
    sofar:=[0:i in [1..M`LevelData`total_number_of_one_orbits]];
    
    //We know the boundary of the standard 2 polytopes.  We get the
    //boundaries of the Gamma0 classes of 2-polytopes by translation.
    for L in boundary do
	//gamma0 moves standard 2-poly to here.
	mover:=L[3];//moves std edge to here
	sgn:=L[2];
	GLtype1:=L[1];
	i:=brm(M,gamma0*mover);
	Gamma0type1:=M`LevelData`one_orbits[GLtype1]`orbit_type[i];
		
	onumber:=M`LevelData`one_orbits[GLtype1]`orbit_number_list[i];
	totsgn:=sgn*onumber;
	j:=M`LevelData`one_orbits[GLtype1]`entry[Gamma0type1];
	sofar[j] +:= totsgn ;
    end for;
    vprintf Bianchi,4: "This relation involves edges %o.\n",
	Support(Vector(sofar));
    return sofar;
end function;

function relations(M)
    //Assumes F and M`LevelData have already been set up correctly
    vprint Bianchi, 1:"Computing relations and non-orientable cells.";
    orbits2:=M`LevelData`two_orbits;
    orbits1:=M`LevelData`one_orbits;
    L:=[];
    for GLtype2 in [1..#orbits2] do
	orbit:=orbits2[GLtype2];
	for Gamma0type2 in [1..orbit`total_number] do
	    if not Gamma0type2 in orbit`non_orientable_orbits then 
		col:=get_column(M,GLtype2,Gamma0type2);
		Append(~L,col);
	    end if;
	end for;
    end for;

    // the above computes the relations coming from the
    // orientable facets of the
    // polytopes.  Now we still must introduce the relations coming from
    // non-orientable orbits of edges.
    noedge_index:=&cat[[edge`entry[i]: i in edge`non_orientable_orbits] : edge in orbits1];
    non_orientables:=[[0: i in [1..M`LevelData`total_number_of_one_orbits]]:
	j in [1..#noedge_index]];
    for i in [1..#noedge_index] do
	non_orientables[i][noedge_index[i]]:=1;
	vprintf Bianchi, 4:
	    "edge number %o is non-orientable.\n", noedge_index[i];
    end for;

    L:=L cat non_orientables;
    vprintf Bianchi, 3:
	"     There are %o relations and %o non-orientable edges.\n",#L,#non_orientables;
    return L;

end function;

forward abmat, unimodularize;

function cusptype(M,alpha,cusplist)
    // given a minimal vector defining a cusp alpha and a list of standard
    // cusps, return the type.  If v is new, return 1+maxtype.  Append
    // v to list of cusplist and return it as well.
    OF := Integers(BaseField(M));
    alpha := unimodularize(M,alpha);
    a1 := alpha[1];
    a2 := alpha[2];
    a := ideal<OF | a1,a2>;
    level := Level(M);
    H,f := ClassGroup(BaseField(M));
    assert a + level eq 1*OF;
    aplist := [ ideal<OF | w[1], w[2]> : w in cusplist ];
    for type in [ 1..#cusplist ] do
	if aplist[type] eq a then
	    ap1 := cusplist[type,1];
	    ap2 := cusplist[type,2];
	    ap := ideal<OF | ap1,ap2>;
	    
	    btype := Position([I@@f : I in M`ModFrmData`ideal_reps],-(a@@f));
	    assert btype ne 0;
	    b := M`ModFrmData`ideal_reps[btype];
	    b1, b2 := Explode(Basis(b));
	    	    
	    M1 := abmat(a1,a2,b);
	    M2 := abmat(ap1,ap2,b);
	   
	    b1 := M1[1,2];
	    b2 := M1[2,2];
	    bp1 := M2[1,2];
	    bp2 := M2[2,2];
	    
	    if (a2*OF + level) eq (ap2*OF + level) then
		//abd2 := a*b*(a2*OF + level);  // I don't think this is right.   
		abd2 := OF!!(a^(-1) * b * ((a2*ap2)*OF) + a*b * level);
		tf := exists(u){u : u in M`ModFrmData`torsion_units |
		    a2*bp2 mod abd2 eq u*ap2*b2 mod abd2};
		if tf then
		    return type, cusplist;
		end if;
	    end if;
	end if;
    end for;
    // if it reaches here, then it is not conjugate to any so far.
    return #cusplist + 1, Append(cusplist,Eltseq(alpha));
end function;

procedure homologydata(M)
    //Attaches a record of the homology
    SetLevel(M);
    OF := Integers(BaseField(M));
    Coeff:=M`homology_coefficients;
    if not assigned  M`LevelData`homology`relations then 
	M`LevelData`homology`relations := relations(M);
    end if;
    M`LevelData`homology`coefficient_ring:=Coeff;

    if not assigned M`LevelData`homology`zero_sharbly_space then 	
	// now try to compute cuspidal part.
	
	boundary := [];
	cuspclasses := [Basis(a) : a in M`ModFrmData`ideal_reps];
	for GLtype in [1..#M`LevelData`one_orbits] do
	    for gamma in M`LevelData`one_orbits[GLtype]`gamma_list do
		alpha :=
		    Eltseq(gamma*Matrix(OF,1,M`ModFrmData`one_poly[GLtype]`O2_vertices[1]));
		atype,cuspclasses := cusptype(M,alpha,cuspclasses);
		beta :=
		    Eltseq(gamma*Matrix(OF,1,M`ModFrmData`one_poly[GLtype]`O2_vertices[2]));
		btype,cuspclasses := cusptype(M,beta,cuspclasses);
		type := [atype, btype];
		if GLtype in M`ModFrmData`zero_reversers then 
		    Append(~boundary,Reverse([atype, btype]));
		else
		    Append(~boundary,type);
		end if;
	    end for;
	end for;
	M`ModFrmData`cuspclasses := cuspclasses;
	
	
	zss:=RSpace(Coeff,M`LevelData`total_number_of_one_orbits);
	// Now need to kill off non-orientable cells and 1-sharbly relations
	rel := M`LevelData`homology`relations;
	mss,mf := quo<zss | rel >;
	
	
	
	// define map from homology space to 
	boundarymap := [];

	for i in [1..M`LevelData`total_number_of_one_orbits] do
	    col := [0 : i in [1..#cuspclasses]];
	    col[boundary[i,1]] := 1;
	    col[boundary[i,2]] +:= -col[boundary[i,1]];
	    Append(~boundarymap,col);
	end for;

	Z := RSpace(M`homology_coefficients,#cuspclasses);
	bmap := Hom(zss,Z)!boundarymap;



	for i in [1..#rel] do
	    assert IsZero(bmap(Vector(rel[i])));
	end for;

	cmap := Hom(mss,Z)![Eltseq(bmap(v@@mf)) : v in Basis(mss)];
	M`bmap := cmap;	
	H,f := NullSpace(cmap);
	M`LevelData`homology`zero_sharbly_space:=zss;
	M`LevelData`homology`H:=H;
	M`LevelData`homology`ToH:= mf; // map from zss to H.
	M`Dimension := Dimension(H);
	
	
	bm:=BasisMatrix(H);
	M`basis_matrix := bm;
	I:=IdentityMatrix(CoefficientRing(bm),NumberOfRows(bm)); 
	M`basis_matrix_inv:=
	    Transpose(Solution(Transpose(M`basis_matrix),I));
    end if;

end procedure;

/*********************************************
* From Geometry/BianchiNew/hackobj.m
**********************************************/

function DimensionBianchi(M)
    vprint Bianchi,1:"Computing dimension of the cuspidal space.";
     if not assigned M`Dimension then 
	homologydata(M);
    end if;
    return M`Dimension; 
end function;

/*********************************************
* From Geometry/BianchiNew/sharbly.m
**********************************************/

function unimodularize(M,v)
    //return v; // don't need to do below.
    //  I think we need this to implement Cremona cusp boundary
    // technique.
	
    //O:=CoefficientRing(v);
    O:=Integers(BaseField(M));
    G,f:=ClassGroup(O);
    I:=ideal<O|v[1],v[2]>;
    GI:=I@@f;
    tf:=exists(stdrep){r :r in M`ModFrmData`ideal_reps|r@@f eq GI};
    _,d:=IsPrincipal(I/stdrep);
    return Vector([O|v[1]/d, v[2]/d]);    
end function;

/*********************************************
* From Geometry/BianchiNew/cuspidal.m
**********************************************/

function abmat(a1,a2,b)
    // given a1, a2 in OF and ideal B, find ab matrix.
    OF := Parent(a1);
    a := ideal<OF | a1,a2>;
    tf,g := IsPrincipal(a*b);
    assert tf;
    
    if a1*a2 eq 0 then
	assert b eq 1*OF;
	if a2 eq 0 then 
	    A:= Matrix(OF,2,[a1,0,0,1/a1]);
	else
	    A :=  Matrix(OF,2,[0,a2,-1/a2,0]);
	end if;
    else

	I := a1/g*b;
	J := a2/g*b;
	tf,i,j := Idempotents(I,J);
	assert i + j eq 1;
	// now i + j = 1.
	b2 := g*i/a1;
	b1 := -j*g/a2;
	
	assert ideal<OF | b1, b2> eq b;
	A :=  Matrix(OF,2,[a1,b1,a2,b2]);
    end if;
    assert ideal<OF| Determinant(A)> eq a*b;
    return A;
end function;
