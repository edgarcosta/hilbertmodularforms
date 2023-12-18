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
                     // generators is nondeterministic.
  MarkedDrchChar, // GrpDrchNFElt - A character psi of the ray residue ring of modulus Modulus(X)
                   // such that psi * chi_inf (the infinity-type associated to the given weight)
                   // is trivial on units (i.e. is a character on principal ideals). 
  MarkedCharClassRepEvals, // Assoc: 
  IsNonempty; // bool: true if there are Grossencharacters of this weight and level

declare attributes HMFGrossenchar:
  Parent, // HMFGrossencharsTorsor
  RayClassChar; // GrpHeckeElt 

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
  G, X`ClassMap := ClassGroup(X`BaseField);
  require IsDiagonal(RelationMatrix(G)) : "There should be no cross-relations\
      between the generators of the ray class group";

  X`ClassGroupReps := [<G.i, X`ClassMap(G.i)> : i in [1 .. #Generators(G)]];
  X`ClassGroup := G;

  if IsNonempty(X) then
    SetMarkedCharClassRepEvals(X);
  end if;
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

intrinsic EvaluateNoncompactInfinityType(X::HMFGrossencharsTorsor, x::FldElt) -> FldElt, FldElt
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
  K := X`BaseField;
  require Parent(x) eq K : "x must be an element of the base field of X";

  places := InfinitePlaces(K);
  r, s := Signature(K);

  // If this is a finite order character, then the weight
  // part of the infinity type is 1. 
  if IsFiniteOrder(X) then
    return Rationals()!1;
  end if;

  K_gal := (IsNormal(K)) select K else SplittingField(K);
  auts := AutsOfKReppingEmbeddingsOfF(K, K_gal);
  gal_conjs_of_x := [aut(x) : aut in auts];
  
  // If the character is algebraic, then the infinity type looks like
  // a product of integral powers. Otherwise, our output will live in 
  // a field extension with some square roots. 
  if IsAlgebraic(X) then
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

intrinsic EvaluateNoncompactInfinityType(X::HMFGrossencharsTorsor, x::RngElt) -> FldElt
  {}
  K := NumberField(Parent(x));
  return  EvaluateNoncompactInfinityType(X, K!x);
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
    if IsFiniteOrder(X) then
      X`IsNonempty := true;
      X`MarkedDrchChar := Dv.0;
    else
      D, D_map := RayResidueRing(mod_fin, mod_inf);
      D_gens := SetToSequence(Generators(D));
      // largest possible order of an element in D
      max_D_order := LCM([Order(gen) : gen in D_gens]);

      // The values of the infinity-type on units and the values of possible
      // Dirichlet characters psi all lie in Q(zeta_m). 
      //
      // Because m can be quite large, we avoid constructing Q(zeta_m). 
      // Instead, we perform the computation to find psi over the complex
      // numbers. 
      d := LargestRootOfUnity(SplittingField(X`BaseField));
      m := LCM(max_D_order, d);
      L := CyclotomicField(d);
      rou_dict := AssociativeArray();
      for j in [0 .. d - 1] do
        rou_dict[L.1^j] := j;
      end for;
      units_gens := UnitsGenerators(X`BaseField : exclude_torsion:=false);
      unit_preimg_seqs := [Eltseq(eps @@ D_map) : eps in units_gens];
      M := [[unit_preimg_seqs[j][i] * ExactQuotient(m, Order(D_gens[i])) : j in [1 .. #units_gens]] : i in [1 .. #D_gens]];
      char_vector := func<i, n, x | [(j eq i) select x else 0 : j in [1 .. n]]>;
      M cat:= [char_vector(j, #units_gens, m) : j in [1 .. #units_gens]];
      M := Matrix(M);
      v := [ExactQuotient(m, d) * rou_dict[StrongCoerce(L, EvaluateNoncompactInfinityType(X, eps))] : eps in units_gens];
      v := Vector(v);
      X`IsNonempty, u := IsConsistent(M, v);
      if X`IsNonempty then
        if #D eq 1 then
          X`MarkedDrchChar := AssociatedPrimitiveCharacter(Dv.0);
        else
          Dv_gens := Generators(Dv);
          // we invert because we want the product of the Dirichlet character
          // and the infinity type to be 1.
          D_gens := [gen : gen in D_gens | Order(gen) ne 1];
          Dv_gens := [gen : gen in SetToSequence(Dv_gens) | Order(gen) ne 1];
          assert #Dv_gens eq #D_gens;
          psi := (&*[Dv.j^(u[j]) : j in [1 .. #D_gens]])^-1;
          X`MarkedDrchChar := AssociatedPrimitiveCharacter(psi);
          for eps in units_gens do
            require IsOne(StrongMultiply(
                  [* EvaluateNoncompactInfinityType(X, eps), X`MarkedDrchChar(eps) *]
                  )) : "The marked character isn't the inverse of the infinity type";
          end for;
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
    if not IsZero(tup[1]) then
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
  // returns the largest divisor of d such that x is a dth root
  divisors := Divisors(d);
  for t in Reverse(divisors) do
    if IsPower(x, t) then
      return t;
    end if;
  end for;
  assert 0 eq 1; // Something has gone wrong, any element should be a first root
end function;

intrinsic SetMarkedCharClassRepEvals(X::HMFGrossencharsTorsor)
  {
    Define the evaluation of a marked element of the set of
    Grossencharacters of this weight on representatives of generators
    of the ray class group.
  }
  if not assigned X`MarkedCharClassRepEvals then
    X`MarkedCharClassRepEvals := AssociativeArray();

    polys := [];
    inf_evals := [];
    L := RationalsAsNumberField();
    reps := [];
    for tup in X`ClassGroupReps do
      gen, rep := Explode(tup);
      d := Order(gen);

      b, x := IsPrincipal(rep^d);
      require b : "Something has gone wrong, rep^d should be a principal ideal";

      a := EvaluateNoncompactInfinityType(X, x) * X`MarkedDrchChar(x);

      t := MaxPowerDividingD(L!a, d);
      L := RadicalExtension(L, Integers()!(d/t), L!a);
      X`MarkedCharClassRepEvals[rep] := Root(L!a, d)^-1;
      Append(~reps, rep);
    end for;
    for rep in reps do
      X`MarkedCharClassRepEvals[rep] := L!X`MarkedCharClassRepEvals[rep];
    end for;
  end if;
end intrinsic;

//////////////////////////////// HMFGrossenchar constructors

intrinsic cHMFGrossenchar(X::HMFGrossencharsTorsor, psi::GrpHeckeElt) -> HMFGrossenchar
  {}
  // check that psi is the right whatnots
  chi := New(HMFGrossenchar);
  chi`Parent := X;
  require Modulus(psi) eq Modulus(X) : "The given ray class character does not have\
      the same modulus as the given parent object";
  chi`RayClassChar := psi;
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
    marked_char_on_J := Rationals()!1;
  else
    I_CG := I @@ X`ClassMap; 
    J := X`ClassMap(I_CG);

    // We choose a generator for IJ^-1. 
    c, x := IsPrincipal(I * J^-1);
    require c : "Something has gone wrong, I * J^-1 should be principal";
    vals := X`ClassGroupReps;
    g := I @@ X`ClassMap;
    g_factzn_exps := Eltseq(g);
    require &+[g_factzn_exps[i] * vals[i][1] : i in [1 .. #vals]] eq g : "Something has gone wrong,\ 
      Eltseq(g) should give a factorization of g in terms of the generators of the class group."; 
    marked_char_on_J := &*[X`MarkedCharClassRepEvals[vals[i][2]]^(g_factzn_exps[i]) : i in [1 .. #vals]];
  end if;

  return StrongMultiply([*
      chi`RayClassChar(I),
      marked_char_on_J,
      EvaluateNoncompactInfinityType(X, x)^-1,
      X`MarkedDrchChar(X`BaseField!x)^-1 
      *]);
end intrinsic;

//////////////////////////////// HMFGrossenchar attribute access

intrinsic Conductor(chi::HMFGrossenchar) -> RngOrdIdl
  {}
  X := Parent(chi);
  return Conductor(X`MarkedDrchChar * DirichletRestriction(chi`RayClassChar)^-1);
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
