/******************************************************************************
 * The HMFGrossenchar type represents a Hecke character over a specified
 * base field of a given infinity-type and level. While the set of Grossencharacters
 * of a given infinity-type and level is a torsor for the corresponding ray class group,
 * there is no canonical way to identify the two sets. 
 *
 * As such, the HMFGrossencharsTorsor constructs an arbitrary element of this set,
 * and its children objects are instances of HMFGrossenchar, each obtained by multiplying
 * its parent's arbitrary element by a ray class character.
 *
 * Magma provides an implementation of Grossencharacters but it is restricted to
 * algebraic finite-order characters, and we want neither of these restrictions. 
 ******************************************************************************/

declare type HMFGrossencharsTorsor [HMFGrossenchar];
declare attributes HMFGrossencharsTorsor:
  BaseField, // FldNum - A number field, say with r real places and s complex places
  Weight, // SeqEnum[Tup[FldRatElt, FldRatElt]] - A sequence of the form
          //   [<a_1, 0> ..., <a_r, 0>, <u_(r+1), v_(r+1)>, ..., <u_s, v_s>]
          //   where r and s are as above and the a_i, u_i, and v_i are rational numbers.
          //   Such a weight corresponds to the infinity-type 
          //   \prod |x_i|^a_i * \prod z_j^u_j zbar_j^v_j,
          //   ignoring the signs at the real places (which are handled elsewhere).
  FiniteModulus, // RngOrdIdl - The finite modulus 
  InfiniteModulus, // SeqEnum[RngOrdInt] - The infinite modulus 
  ClassGroup, ClassMap, // GpAb, Map -  cached output of ClassGroup(X`BaseField),
  ClassGroupReps, // SeqEnum[Tup[GpAbElt, RngOrdIdl]] - A sequence consisting of 
                     // generators for the class group and corresponding ideal 
                     // representatives. We do this because the algorithm for computing
                     // generators is nondeterministic, and because we want to use
                     // generators which are coprime to the modulus of the character.
  MarkedDrchChar, // GrpDrchNFElt - A character psi of the ray residue ring of modulus Modulus(X)
                   // such that psi * chi_inf (the infinity-type associated to the given weight)
                   // is trivial on units (i.e. is a character on principal ideals). 
  MarkedCharClassRepEvals, // Assoc: I -> chi_0(I), where I is one of the ideals appearing in
                           //   X`ClassGroupReps and where chi_0 is the marked Grossencharacter
                           //   of the torsor.
  IsNonempty; // bool: true if there are Grossencharacters of this weight and level

declare attributes HMFGrossenchar:
  Parent, // HMFGrossencharsTorsor
  RayClassChar, // GrpHeckeElt 
  ClassRepEvals, // Assoc - I -> chi(I), where I is one of the ideals appearing in
                       //   X`ClassGroupReps and where chi_0 is the marked Grossencharacter
                       //   of the torsor.
  DrchChar, // GrpDrchNFElt - The primitive character associated to the product of 
            //  the marked Dirichlet character of the torsor and
            //  the Dirichlet restriction of the ray class character 
            //  attached to this Grossencharacter. The conductor of this
            //  character is the conductor of the Grossencharacter.
  IsPrimitivized; // BoolElt - true if the character has been primitivized, i.e.
                  // if the conductor of chi`DrchChar is equal to the conductor
                  // of chi. If true, chi can be evaluated at any ideal
                  // coprime to its conductor, but if false it is only 
                  // guaranteed to be evaluable at ideals coprime to the
                  // modulus.

//////////////////////////////// HMFGrossencharsTorsor ////////////////////////////////

//////////////////////////////// HMFGrossencharsTorsor constructors

intrinsic cHMFGrossencharsTorsor(
    K::FldNum,
    k::SeqEnum,
    N_f::RngOrdIdl :
    N_oo:=[1 .. #RealPlaces(K)]
   ) -> HMFGrossencharsTorsor
  {
    inputs:
      K - A Galois number field
      k - A weight, as described above
      N_f - A finite modulus 
      N_oo - An infinite modulus
    returns:
      A type representing the set of Grossencharacters over K
      with weight k, finite modulus N_f, and infinite modulus N_oo

    Basic constructor 
  }
  X := New(HMFGrossencharsTorsor);
  X`BaseField := K;
  X`Weight := k;
  X`FiniteModulus := N_f;
  X`InfiniteModulus := N_oo;
  X`ClassGroup, X`ClassMap := ClassGroup(X`BaseField);
  require IsDiagonal(RelationMatrix(X`ClassGroup)) : "There should be no cross-relations\
      between the generators of the class group";

  // TODO abhijitm - it'd be nice to someday remove this requirement
  // but I don't have any plans to.
  if not IsAlgebraic(X) then
    require IsCM(K) : "Nonalgebraic characters are currently only supported over CM base fields";
  end if;

  // This is a very important function, which checks if there is a Dirichlet character
  // which cancels out the infinity part. 
  _ := IsNonempty(X);
  return X;
end intrinsic;

intrinsic HMFGrossencharsTorsorSet(X::HMFGrossencharsTorsor) -> SetEnum
  {
    Returns the set of HMFGrossenchar objects of this torsor. 
    This set will either be empty or have cardinality equal
    to that of HeckeCharacterGroup(Modulus(X)).
  }
  N_f, N_oo := Modulus(X); 
  H := HeckeCharacterGroup(N_f, N_oo);
  out := {};
  if IsNonempty(X) then
    for chi in Elements(H) do
      Include(~out, cHMFGrossenchar(X, chi));
    end for;
  end if;
  
  if not IsNonempty(X) then
    require #out eq 0 : "Something has gone wrong - if the torsor is empty,\
      the set should be empty";
  else
    require #out eq #H : "Something has gone wrong, this set should be in 1-1 correspondence\
      with characters of the corresponding ray class group.";
  end if;
  return out;
end intrinsic;

intrinsic HMFGrossencharsTorsorSet(K::FldNum, k::SeqEnum[Tup], N::RngOrdIdl) -> SetEnum
  {}
  X := cHMFGrossencharsTorsor(K, k, N);
  return HMFGrossencharsTorsorSet(X);
end intrinsic;

//////////////////////////////// HMFGrossencharsTorsor helpers

// TODO abhijitm this function name is unfortunate as it works
// on either a unit of K or an element of K+
function eval_inf_type_at_rou_or_tot_real(X, x)
  /*
   * inputs
   *   X - HMFGrossencharsTorsor, with X`BaseField expected to be a CM field
   *   x - FldElt, with x either a root of unity or an element in K^+
   *   cmplx_conj
   * returns
   *   FldElt, The evaluation of the non-compact infinity type of X at x
   *
   * This function exists to do some hacks in the non-algebraic case which allow
   * us to compute spaces of non-algebraic grossencharacters over a CM field K.
   * The idea is that the units of K are roots of unity in K along with the units
   * of F, and the infinity type can be evaluated on these relatively easily.
   */
  K := X`BaseField;
  b, _, Kplus := IsCM(K);

  // we require that K is CM 
  assert b;

  K_gal := (IsGalois(K)) select K else SplittingField(K);
  // auts is a length 2n list where the last n are complex conjugates
  // of the first n. 
  auts := AutsOfKReppingEmbeddingsOfF(K, K_gal);

  Kplus_deg := ExactQuotient(Degree(K), 2);
  non_conj_auts := auts[1 .. Kplus_deg];

  n_is := [Integers()!(X`Weight[i][1] - X`Weight[i][2]) : i in [1 .. Kplus_deg]];
  s := Integers()!(X`Weight[1][1] + X`Weight[1][2]);
  // In both of the cases below, the character is
  // the character is
  // \prod_i (x_i/|x_i|)^(a_i - b_i) |x_i|^(a_i + b_i)
  if IsRootOfUnity(K_gal!x) then
    // in this case |x_i| = 1 so we just get \prod_i x_i^(a_i-b_i)
    return &*[non_conj_auts[i](K_gal!x)^(n_is[i]) : i in [1 .. Kplus_deg]];
  end if;

  b, x_Kplus := IsStrongCoercible(Kplus, x);
  // This function should only be called when x is either
  // a root of unity or an element of the totally real subfield of K
  assert b;
  vs := InfinitePlaces(K);
  // In this case |Norm(x)| =  and x_i / |x_i| = sign(x_i)
  // so we get \prod_i sign(x_i)^(a_i - b_i)
  return Norm(x_Kplus)^s * &*[Sign(Real(Evaluate(x, vs[i])))^(n_is[i] + s)  : i in [1 .. Kplus_deg]];
end function;

intrinsic EvaluateNoncompactInfinityType(X::HMFGrossencharsTorsor, x::FldElt : nonpar_hack:=false) -> FldElt, FldElt
  {
    inputs:
      X - a torsor of HMFs of a given field K, level N, weight k
      x - An element of the field K
    returns:
      If the weight k is
      [<a_1, b_1>, ..., <a_r, b_r>, <u_(r+1), v_(r+1)>, ..., <u_s, v_s>],
      evaluates the "non-sign" part of the infinity-type on x,
      i.e. the map x -> \prod |x_i|^a_i * \prod z_j^u_j zbar_j^v_j,
      where the first product is over the embeddings under real places
      and the latter is over the embeddings under imaginary places.

      This is the evaluation of the infinity-type with the \prod sgn(x_i)^b_i 
      (over the embeddings under real places) omitted. We deal with the 
      sign part elsewhere.
  }

  if nonpar_hack then
    return eval_inf_type_at_rou_or_tot_real(X, x);
  end if;
    
  K := X`BaseField;
  require Parent(x) eq K : "x must be an element of the base field of X";

  places := InfinitePlaces(K);
  r, s := Signature(K);

  // If this is a finite order character, then the weight
  // part of the infinity type is 1. 
  if IsFiniteOrder(X) then
    return Rationals()!1;
  end if;

  K_gal := (IsGalois(K)) select K else SplittingField(K);
  auts := AutsOfKReppingEmbeddingsOfF(K, K_gal);
  gal_conjs_of_x := [aut(x) : aut in auts];
  
  // If the character is algebraic, then the infinity type looks like
  // a product of integral powers. Otherwise, our output will live in 
  // a field extension with some square roots, unless x happens to be
  // a square anyways.
  if IsAlgebraic(X) or IsSquare(x) then
    L := K_gal;
  else
    R<z> := PolynomialRing(K);
    polys := [];
    for i->y in gal_conjs_of_x do
      append_sqrt := false;
      if (i le r + s) and not IsIntegral(X`Weight[i][1]) then
        append_sqrt := true;
      elif (i gt r + s) and not IsIntegral(X`Weight[i - s][2]) then
        append_sqrt := true;
      end if;

      if append_sqrt then
        poly := x^2-y;
        if IsIrreducible(x^2-y) then
          Append(~polys, poly);
        end if;
      end if;
    end for;
    L := (#polys eq 0) select K else AbsoluteField(ext<K | polys>);
  end if;

  out := L!1;
  for i->y in gal_conjs_of_x do
    if i le r then
      u_i := X`Weight[i][1];
      out *:= (L!y)^(u_i);
    elif i le (r + s) then
      u_i := X`Weight[i][1];
      out *:= (L!y)^(u_i);
    else
      v_i := X`Weight[i - s][2];
      out *:= (L!y)^(v_i);
    end if;
  end for;

  return out;
end intrinsic;

intrinsic EvaluateNoncompactInfinityType(X::HMFGrossencharsTorsor, x::RngElt : nonpar_hack:=false) -> FldElt
  {}
  K := NumberField(Parent(x));
  return  EvaluateNoncompactInfinityType(X, K!x : nonpar_hack:=nonpar_hack);
end intrinsic;

intrinsic IsNonempty(X::HMFGrossencharsTorsor) -> BoolElt, GrpDrchNFElt
  {
    Suppose X has modulus m (note that this is both the finite level N
    and the ramified real places), base field F, and non-compact
    infinity-type chi_nc. 

    Returns true, psi if there is a Dirichlet character with modulus m
    such that psi(eps) * chi_nc(eps) = 1 for all units eps of F,
    and assigns X`MarkedDrchChar := psi

    Otherwise, returns false, _.

    If such a psi exists, psi * chi_nc is a character on
    principal ideals, and we can extend it to a character on ideals.
  }
  if not assigned X`IsNonempty then
    mod_fin, mod_inf := Modulus(X);
    Dv := DirichletGroup(mod_fin, mod_inf);
    
    nonpar_hack := not IsAlgebraic(X);
    if IsFiniteOrder(X) then
      X`IsNonempty := true;
      X`MarkedDrchChar := Dv.0;
      elif &and[IsOne(EvaluateNoncompactInfinityType(X, eps : nonpar_hack:=nonpar_hack)) : eps in UnitsGenerators(X`BaseField : exclude_torsion:=false)] then
      X`IsNonempty := true;
      X`MarkedDrchChar := Dv.0;
    else
      K := X`BaseField;
      E := (IsGalois(K)) select K else SplittingField(K);
      D, D_map := RayResidueRing(mod_fin, mod_inf);
      D_gens := SetToSequence(Generators(D));
      // largest possible order of an element in D
      max_D_order := LCM([Order(gen) : gen in D_gens]);

      // The values of the infinity-type on units and the values of possible
      // Dirichlet characters psi all lie in Q(zeta_m). 
      //
      // Because m can be quite large, we avoid constructing Q(zeta_m). 
      d, zeta_d := LargestRootOfUnity(E);
      m := LCM(max_D_order, d);
      // a dth root of unity in K
      // the copy of Q(zeta_d) inside of v 
      rou_dict := AssociativeArray();
      for j in [0 .. d - 1] do
        rou_dict[zeta_d^j] := j;
      end for;
      units_gens := UnitsGenerators(X`BaseField : exclude_torsion:=false);
      unit_preimg_seqs := [Eltseq(eps @@ D_map) : eps in units_gens];
      M := [[unit_preimg_seqs[j][i] * ExactQuotient(m, Order(D.i)) : j in [1 .. #units_gens]] : i in [1 .. #D_gens]];
      // returns a length n seqenum which is 0s except at the ith position, where it's n
      char_vector := func<i, n, x | [(j eq i) select x else 0 : j in [1 .. n]]>;
      M cat:= [char_vector(j, #units_gens, m) : j in [1 .. #units_gens]];
      M := Matrix(M);
      v := [ExactQuotient(m, d) * rou_dict[EvaluateNoncompactInfinityType(X, eps : nonpar_hack:=nonpar_hack)] : eps in units_gens];
      v := Vector(v);
      
      X`IsNonempty, u := IsConsistent(M, v);
      if X`IsNonempty then
        if #D eq 1 then
          X`MarkedDrchChar := AssociatedPrimitiveCharacter(Dv.0);
        else
          Dv_gens := Generators(Dv);
          D_gens := [gen : gen in D_gens | Order(gen) ne 1];
          Dv_gens := [gen : gen in SetToSequence(Dv_gens) | Order(gen) ne 1];
          assert #Dv_gens eq #D_gens;
          // we invert because we want the product of the Dirichlet character
          // and the infinity type to be 1.
          psi_cand := (&*[Dv.j^(u[j]) : j in [1 .. #D_gens]])^-1;

          // function to check if psi is the inverse of the noncompact infinity type 
          // on all units of K
          psi_works := func<psi | &and[IsOne(StrongMultiply(
                    [* EvaluateNoncompactInfinityType(X, eps : nonpar_hack:=nonpar_hack), psi(eps) *]
                  )) : eps in units_gens]>;
          if d eq 2 then
            require psi_works(psi_cand) : "psi isn't the inverse of the infinity type,
                       something's wrong!";
            psi_true := psi_cand;
          else
            // In this case, we have to deal with some stupidity involving embeddings 
            // of the root of unity. TODO abhijitm I couldn't figure out how to do this 
            // cleanly, so I decided to just loop through odd powers until one of the psi
            // worked (this is fine at least for totally real and CM base fields 
            // because it'll already be correct on the totally real units since those evaluations
            // are +/- 1 and what's left is checking on the root of unity
            flag := false;
            for i in [2*j - 1 : j in [1 .. d]] do
              psi := psi_cand^i;
              if psi_works(psi) then
                flag := true;
                psi_true := psi;
                break i;
              end if;
            end for;
            require flag : "Something is wrong, some power of psi_cand should've worked";
          end if;
          X`MarkedDrchChar := AssociatedPrimitiveCharacter(psi_true);
        end if;
      end if;
    end if;
  end if;

  if X`IsNonempty then
    require assigned X`MarkedDrchChar : "If X is nonempty them the marked\
      Dirichlet character must be assigned";
    return true, X`MarkedDrchChar;
  else
    return false, _;
  end if;
end intrinsic;

intrinsic ClassGroupReps(X::HMFGrossencharsTorsor) -> SeqEnum[Tup]
  {
    Let K = X`BaseField. This function returns a sequence consisting of tuples 
    of <g, I>, where g is a group element of the class group and I is an ideal 
    of O_K in the class g that is coprime to the finite modulus of X. 
  }
  if not assigned X`ClassGroupReps then
    if #X`ClassGroup eq 1 then
      return [];
    end if;
    rcg, rc_map:= RayClassGroup(X`FiniteModulus, X`InfiniteModulus);
    cg_gens := Generators(X`ClassGroup);
    cg_gens_og := cg_gens;
    cg_reps_dict := AssociativeArray();

    // find a subset of ideal generators of the ray class group 
    // which generate the class group. The point is to find
    // generators which are coprime to the finite modulus so that
    // we don't encounter trouble when evaluating things.
    for rc_gen in Generators(rcg) do
      I := rc_map(rc_gen);
      cg_img_of_gen := I @@ X`ClassMap;
      if not IsDefined(cg_reps_dict, cg_img_of_gen) then
        cg_reps_dict[cg_img_of_gen] := I;
      else
        if Norm(I) lt Norm(cg_reps_dict[cg_img_of_gen]) then
          cg_reps_dict[cg_img_of_gen] := I;
        end if;
      end if;
    end for;
    X`ClassGroupReps := [<gen, cg_reps_dict[gen]> : gen in cg_gens_og];
    for tup in X`ClassGroupReps do
      assert tup[2] @@ X`ClassMap eq tup[1];
      assert IsCoprime(tup[2], X`FiniteModulus);
    end for;
  end if;
  return X`ClassGroupReps;
end intrinsic;

//////////////////////////////// HMFGrossencharsTorsor fundamental intrinsics

intrinsic Print(X::HMFGrossencharsTorsor, level::MonStgElt)
  {}
  if level in ["Default", "Minimal", "Maximal"] then
    printf "Grossencharacters over the %o\n", X`BaseField;
    printf "with weight %o ", X`Weight;
    printf "and finite modulus%o\n", IdealOneLine(X`FiniteModulus);
  elif level eq "Magma" then
    error "not implemented yet!";
  else
    error "not a valid printing level.";
  end if;
end intrinsic;

intrinsic 'eq'(X_1::HMFGrossencharsTorsor, X_2::HMFGrossencharsTorsor) -> BoolElt
  {}
  if X_1`BaseField eq X_2`BaseField and 
    X_1`Weight eq X_2`Weight and
    X_1`FiniteModulus eq X_2`FiniteModulus then
    return true;
  else
    return false;
  end if;
end intrinsic;

//////////////////////////////// HMFGrossencharsTorsor attribute access

intrinsic Modulus(X::HMFGrossencharsTorsor) -> RngOrdIdl, SeqEnum[RngIntElt]
  {}
  return X`FiniteModulus, X`InfiniteModulus;
end intrinsic;

intrinsic IsFiniteOrder(X::HMFGrossencharsTorsor) -> BoolElt
  {}
  for tup in X`Weight do
    if not (IsZero(tup[1]) and IsZero(tup[2])) then
      return false;
    end if;
  end for;
  return true;
end intrinsic;

intrinsic IsAlgebraic(X::HMFGrossencharsTorsor) -> BoolElt
  {}
  for tup in X`Weight do
    if not (IsIntegral(tup[1]) and IsIntegral(tup[2])) then
      return false;
    end if;
  end for;
  return true;
end intrinsic;

//////////////////////////////// HMFGrossencharsTorsor evaluation

function MaxPowerDividingD(x, d)
  // returns the largest divisor of d such that x is a dth power 
  divisors := Divisors(d);
  for t in Reverse(divisors) do
    if IsPower(x, t) then
      return t;
    end if;
  end for;
  assert 0 eq 1; // Something has gone wrong, any element should be a first root
end function;

intrinsic MarkedCharClassRepEvals(X::HMFGrossencharsTorsor) -> Assoc
  {
    Returns an associative array taking an ideal generator I of the class group
    to the evaluation of the marked character of X on I. The Is are drawn from
    ClassGroupReps(X).
  }
  if not assigned X`MarkedCharClassRepEvals then
    X`MarkedCharClassRepEvals := AssociativeArray();

    polys := [];
    inf_evals := [];
    reps := [];
    for tup in ClassGroupReps(X) do
      gen, rep := Explode(tup);
      d := Order(gen);

      b, x := IsPrincipal(rep^d);
      require b : "Something has gone wrong, rep^d should be a principal ideal";

      a := StrongMultiply([* EvaluateNoncompactInfinityType(X, x), X`MarkedDrchChar(x) *]);
      L := Parent(a);
      t := MaxPowerDividingD(a, d);
      L := AbsoluteField(RadicalExtension(L, Integers()!(d/t), Root(a,t)));
      X`MarkedCharClassRepEvals[rep] := Root(L!a, d)^-1;
      Append(~reps, rep);
    end for;
  end if;
  return X`MarkedCharClassRepEvals;
end intrinsic;

//////////////////////////////// HMFGrossenchar constructors

intrinsic cHMFGrossenchar(X::HMFGrossencharsTorsor, psi::GrpHeckeElt) -> HMFGrossenchar
  {}
  chi := New(HMFGrossenchar);
  chi`Parent := X;
  require IsNonempty(X) : "This HMFGrossencharsTorsor is empty!";
  require Modulus(psi) eq Modulus(X) : "The given ray class character does not have\
      the same modulus as the given parent object";
  chi`RayClassChar := psi;
  chi`ClassRepEvals := AssociativeArray();
  for tup in ClassGroupReps(X) do
    rep := tup[2];
    chi`ClassRepEvals[rep] := StrongMultiply([* MarkedCharClassRepEvals(X)[rep], psi(rep) *]);
  end for;
  chi`DrchChar := X`MarkedDrchChar * DirichletRestriction(psi)^-1;
  return chi;
end intrinsic;

//////////////////////////////// HMFGrossenchar fundamental intrinsics

intrinsic Parent(chi::HMFGrossenchar) -> HMFGrossencharsTorsor
  {}
  return chi`Parent;
end intrinsic;

intrinsic 'eq'(chi_1::HMFGrossenchar, chi_2::HMFGrossenchar) -> BoolElt
  {}
  if (chi_1`Parent eq chi_2`Parent) and (chi_1`RayClassChar eq chi_2`RayClassChar) then
    return true;
  else
    return false;
  end if;
end intrinsic;

intrinsic Print(chi::HMFGrossenchar, level::MonStgElt)
  {}
  if level in ["Default", "Minimal", "Maximal"] then
    printf "Grossencharacter element associated to the ray class character %o\nin the set of ", chi`RayClassChar;
    print Parent(chi);
  elif level eq "Magma" then
    error "not implemented yet!";
  else
    error "not a valid printing level.";
  end if;
end intrinsic;

intrinsic '@'(I::RngOrdIdl, chi::HMFGrossenchar) -> FldElt
  {}
  X := Parent(chi);
  b, x := IsPrincipal(I);

  if b then
    chi_at_J := Rationals()!1;
  else
    g := I @@ X`ClassMap; 
    g_factzn_exps := Eltseq(g);
    cg_reps := ClassGroupReps(X);
    require &+[g_factzn_exps[i] * cg_reps[i][1] : i in [1 .. #cg_reps]] eq g : "Something has gone wrong,\
      Eltseq(g) should give a factorization of g in terms of the generators of the class group."; 
    J := &*[cg_reps[i][2]^(g_factzn_exps[i]) : i in [1 .. #cg_reps]];

    // We choose a generator for IJ^-1. 
    c, x := IsPrincipal(I * J^-1);
    require c : "Something has gone wrong, I * J^-1 should be principal";
    chi_at_J := &*[chi`ClassRepEvals[cg_reps[i][2]]^(g_factzn_exps[i]) : i in [1 .. #cg_reps]];
  end if;

  return StrongMultiply([*
      chi_at_J^-1,
      EvaluateNoncompactInfinityType(X, x),
      chi`DrchChar(X`BaseField!x)
      *]);
end intrinsic;

//////////////////////////////// HMFGrossenchar attribute access

intrinsic Conductor(chi::HMFGrossenchar) -> RngOrdIdl
  {}
  return Conductor(chi`DrchChar);
end intrinsic;

intrinsic Modulus(chi::HMFGrossenchar) -> RngOrdIdl
  {}
  return Modulus(Parent(chi));
end intrinsic;

intrinsic IsAlgebraic(chi::HMFGrossenchar) -> RngOrdIdl
  {}
  return IsAlgebraic(Parent(chi));
end intrinsic;

intrinsic IsFiniteOrder(chi::HMFGrossenchar) -> RngOrdIdl
  {}
  return IsFiniteOrder(Parent(chi));
end intrinsic;

intrinsic IsPrimitivized(chi::HMFGrossenchar) -> BoolElt
  {}
  if not assigned chi`IsPrimitivized then
    chi`IsPrimitivized := IsPrimitive(chi`DrchChar);
  end if;
  return chi`IsPrimitivized;
end intrinsic;

intrinsic IsPrimitive(chi::HMFGrossenchar) -> BoolElt
  {}
  N_f, N_oo := Conductor(chi);
  M_f, M_oo := Modulus(chi);
  return N_f eq M_f and N_oo eq M_oo;
end intrinsic;

intrinsic Primitivize(chi::HMFGrossenchar)
  {
    Given a HMFGrossenchar chi, replaces its Dirichlet character psi
    with the primitive Dirichlet character associated to psi. 

    This is not the same behavior as AssociatedPrimitiveCharacter 
    because this modifies the existing character rather than returning
    a new one in the lower modulus. The point is that if we want to 
    evaluate a ray class character at primes coprime to its conductor
    but not to its modulus, it is better to call this function and then
    perform evaluations rather than to build a whole new character, since
    primitivization does not change anything about the character other
    than "unextending by zero". 
  }
  if not IsPrimitivized(chi) then
    chi`DrchChar := AssociatedPrimitiveCharacter(chi`DrchChar);
    chi`IsPrimitivized := true;
  end if;
end intrinsic;


