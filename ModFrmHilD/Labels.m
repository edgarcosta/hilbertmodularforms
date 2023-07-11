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
