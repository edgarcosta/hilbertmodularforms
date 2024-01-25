import "CongruenceSubgroup.m" : GAMMA_Type, GAMMA_0_Type, GAMMA_1_Type;

intrinsic LMFDBLabel(F::FldNum) -> MonStgElt
 { LMFDB label for quadratic fields }
 n := Degree(F);
 require n eq 2: "only quadratic fields for now";
 D := Discriminant(Integers(F));
 require DefiningPolynomial(F) eq MinimalPolynomial(Integers(QuadraticField(D)).2): "We expect the defining polynomial for F to be minimal, i.e., polredabs";
 real_places := D gt 0 select 2 else 0;
 return Sprintf("%o.%o.%o.1", n, real_places, Abs(D));
end intrinsic;

intrinsic LMFDBField(label::MonStgElt) -> FldNum
  {Given an LMFDB label for a number field, return that field}
  deg, r, D, i := Explode([StringToInteger(el) : el in Split(label, ".")]);
  require deg eq 2: "Only for quadratic fields for now";
  return NumberField(MinimalPolynomial(Integers(QuadraticField(D)).2));
end intrinsic;

intrinsic AmbientTypeLabel(AmbientType::Cat) -> MonStgElt
{ TODO }
     case AmbientType:
        when GLPlus_Type: return "gl";
        when SL_Type: return "sl";
    else
        error "Ambient type not supported.";
    end case;
end intrinsic;

intrinsic GammaTypeLabel(GammaType::MonStgElt) -> MonStgElt
{ TODO }
    case GammaType:
        when GAMMA_Type: return "f";
        when GAMMA_0_Type: return "0";
        when GAMMA_1_Type: return "1";
    else
        error "Gamma type not supported.";
    end case;
end intrinsic;

intrinsic LMFDBLabel(G::GrpHilbert) -> MonStgElt
  {LMFDB label for the congruence subgroups associated to Hilbert modular forms}
  if not assigned G`LMFDBlabel then
      F := BaseField(G);
      field_label := LMFDBLabel(F);
      level_label := LMFDBLabel(Level(G));
      Cl, mp := NarrowClassGroup(F);
      mpdet := IdealRepsMapDeterministic(F, mp);
      comp_label := LMFDBLabel(mpdet[ComponentIdeal(G) @@ mp]);
      ambient_label := AmbientTypeLabel(AmbientType(G));
      gamma_label := GammaTypeLabel(GammaType(G));
      G`LMFDBlabel := Join([field_label, level_label, comp_label, ambient_label, gamma_label], "-");
  end if;
  return G`LMFDBlabel;
end intrinsic;


intrinsic LMFDBCongruenceSubgroup(s::MonStgElt) -> GrpHilbert
 {CongruenceSubgroup given by the label}
    field, level, bb, ambient, gamma := Explode(Split(s, "-"));
    AmbientType := [elt[2] : elt in [<"gl", "GL+">, <"sl", "SL">] | elt[1] eq ambient][1];
    GammaType := [elt[2] : elt in [<"f", "Gamma">, <"0", "Gamma0">, <"1", "Gamma1">] | elt[1] eq gamma][1];
    F := LMFDBField(field);
    NN := LMFDBIdeal(F, level);
    bb := LMFDBIdeal(F, bb);
    G := CongruenceSubgroup(AmbientType, GammaType, F, NN, bb);
    assert LMFDBLabel(G) eq s;
    return G;
end intrinsic;

function sorted_r_tuples(A, r)
  n := #A;
  B := [];
  for i in [0 .. n^r-1] do
    idxs_minus_one := [Integers()!((i - (i mod n^(j-1))) / (n^(j-1))) mod n: j in [1 .. r]];
    Append(~B, [A[idxs_minus_one[j] + 1] : j in [1 .. r]]);
  end for;
  return B;
end function;

intrinsic HackyFieldLabel(F::FldNum) -> MonStgElt
  {
    Given a number field, returns the .-separated coefficients of the 
    defining polynomial as a string.

    For our current handling of coefficient and index fields, as long as 
    two number fields have the same defining polynomial, they will behave
    identically, hence this approach. Once FldNumCC or something like it
    is natively implemented, we may be able to do better.
  }
  return Join([IntegerToString(a) : a in DefiningPolyCoeffs(F)], ".");
end intrinsic;

intrinsic FieldFromHackyLabel(F_label::MonStgElt) -> Fld
  {
    Return the field associated to a field label.

    If the field is quadratic, then we return the FldQuad object
    rather than the degree two number field. Otherwise, we return
    the number field defined by the polynomial with the given coefficients.
  }
  R<x> := PolynomialRing(Rationals());
  def_poly_coeffs := [StringToInteger(x) : x in Split(F_label, ".")];
  if #def_poly_coeffs eq 3 and def_poly_coeffs[2] eq 0 then
    F := QuadraticField(-1*def_poly_coeffs[1]);
  else
    def_poly := elt<R | def_poly_coeffs>;
    F := NumberField(def_poly);
  end if;
  return F;
end intrinsic;

intrinsic CanonicalRayClassGenerators(N_f::RngOrdIdl, N_inf::SeqEnum[RngIntElt]) -> SeqEnum[RngOrdIdl]
  {
    Returns a canonical set of generators for the ray class group with modulus (N_f, N_inf).

    Let r be the smallest size of a set of ideals generating the ray class group 
    dual to the Hecke character group in which chi lies. We choose a canonical
    set of generators by searching in canonical order through ideals up to norm B
    where B is Minkowksi bound times the norm of N -- every ray class is guaranteed 
    to contain an ideal of norm at most B -- representing primitive elements of the 
    ray class group. Whenever an ideal increases the size of the group we generate,
    we add it to our generating set. This process is guaranteed to terminate (because
    the primitive elements contain a generating set) and in fact will terminate with
    a set of exactly r ideals.
  }
  F := NumberField(Order(N_f));
  G, mp := RayClassGroup(N_f, N_inf);

  // deal with trivial group
  if #G eq 1 then
    return [];
  end if;

  gen_order_primes := {* Factorization(Order(G.i))[1][1] : i in [1 .. NumberOfGenerators(G)] *};

  pi := Pi(RealField());
  B := Ceiling(MinkowskiConstant(F) * Norm(N_f));
  ideals := PrimesUpTo(B, F : coprime_to:=N_f);

  reps := [];
  repped_gs := {};
  repped_gs_subgp := sub<G | G.0>;
  g_repping_idls := [];
  for I in ideals do
    g := I @@ mp;
    if not (g in repped_gs_subgp) then
      Include(~repped_gs, g);
      Append(~g_repping_idls, I);
      repped_gs_subgp := sub<G | repped_gs>;
    end if;
  end for;

  require repped_gs_subgp eq G : "your set doesn't generate";
  return g_repping_idls;
end intrinsic;

intrinsic DiscreteLogDict(K::FldCyc) -> Assoc
  {
    Given a cyclotomic field K = Q(zeta_d), where 
    zeta_d = cos(2*pi*i/d) + i sin(2*pi*i/d) in the distinguished 
    embedding of K, return a dict taking zeta^j to j.
  }
  d := CyclotomicOrder(K);
  // in case Magma changes the way it chooses primitive elements
  // or orders its infinite places
  zeta_cc := Evaluate(K.1, MarkedEmbedding(K));
  pi := Pi(RealField());
  i := ComplexField().1;
  require Abs(zeta_cc - (Cos(2*pi/d) + i*Sin(2*pi/d))) lt pi/d : "You should\
    update the code to pick the 'standard' dth root of unity in K with respect\
    to the marked embedding. Abhijit was too lazy to do it because he only\
    needed to work with presentations where K.1 was this.";
  dlog_dict := AssociativeArray();
  for j in [0 .. d-1] do
    dlog_dict[K.1^j] := j;
  end for;
  return dlog_dict;
end intrinsic;

intrinsic HeckeCharLabel(chi::GrpHeckeElt : full_label:=true) -> MonStgElt
  {
    If full_label is true, returns a label for chi including a label for the field
    and ideal. 

    If full_label is false, does not not include the field and ideal labels.

    If I_1, .., I_r is the sequence of generating elements, then
    chi_label consists of the r integers a_i such that chi(I_j) = zeta^(a_i),
    where zeta = cos(2*pi/d) + i*sin(2*pi/d) in the marked embedding of 
    the cyclotomic field where the image of chi lies. 
  }
  F := NumberField(Order(Modulus(chi)));
  N_f, N_inf := Modulus(Parent(chi));
  d := Order(chi);

  K := CyclotomicField(d);
  rcg_gens := CanonicalRayClassGenerators(N_f, N_inf);
  dlog_dict := DiscreteLogDict(K);
  exps := [dlog_dict[chi(gen)] : gen in rcg_gens]; 
  exps_label := Join([IntegerToString(x) : x in exps], ".");
  inf_label := Join([IntegerToString(x) : x in N_inf], ".");
  // we want our label to end with 'u' to make parsing the output easier
  chi_label := Join([IntegerToString(d), exps_label, inf_label, ""], "u");

  // by default we only return the label for chi,
  // since this is used by the SaveAndLoad function which 
  // handles labels for F and N on its own
  if not full_label then
    return chi_label;
  else
    F_label := HackyFieldLabel(F);
    N_label := LMFDBLabel(N_f);
    label_cmpnts := [F_label, N_label, chi_label];
    return Join(label_cmpnts, "_");
  end if;
end intrinsic;

intrinsic FullChiLabelToHeckeChar(full_label::MonStgElt) -> GrpHeckeElt
  {}
  F_label, N_f_label, chi_label := Explode(Split(full_label, "_"));
  F := FieldFromHackyLabel(F_label);
  N_f := LMFDBIdeal(F, N_f_label);
  return ChiLabelToHeckeChar(chi_label, N_f);
end intrinsic;

intrinsic ChiLabelToHeckeChar(
  chi_label::MonStgElt,
  N_f::RngOrdIdl
  ) -> GrpHeckeElt
  {
    inputs:
      chi_label - a short label (full_label:=false) produced by HeckeCharLabel above
      N_f - an ideal such that chi_label is a character of finite modulus N_f
    returns:
      A character chi of finite modulus N_f such that the evaluations of chi on
      the standard generating set
      
    Given a short label, loads the corresponding Hecke character.
  } 
  F := NumberField(Order(N_f));
  d_str, exps_label, inf_label := Explode(Split(chi_label, "u" : IncludeEmpty:=true));

  N_inf := [StringToInteger(x) : x in Split(inf_label, ".")];

  require #N_inf le Degree(F) : "The given ramification\
      at infinity is not compatible with the number field";
  if #N_inf ne 0 then
    require Max(N_inf) le Degree(F) : "The given ramification\
      at infinity is not compatible with the number field";
  end if;

  d := StringToInteger(d_str);
  H := HeckeCharacterGroup(N_f, N_inf);

  if d eq 1 then
    // trivial character
    return H.0;
  end if;
    
  rcg_gens := CanonicalRayClassGenerators(N_f, N_inf);
  exps := [StringToInteger(x) : x in Split(exps_label, ".")];
  K := CyclotomicField(d);
  dlog_dict := DiscreteLogDict(K);
  for chi in Elements(H) do
    if Order(chi) eq d then
      if [dlog_dict[chi(gen)] : gen in rcg_gens] eq exps then
        return chi;
      end if;
    end if;
  end for;
  require 0 eq 1 : "Something's wrong!";
end intrinsic;
