
intrinsic LMFDBLabel(F::FldNum) -> MonStgElt
 { LMFDB label for quadratic fields }
 n := Degree(F);
 require n eq 2: "only quadratic fields for now";
 D := Discriminant(Integers(F));
 real_places := D gt 0 select 2 else 0;
 return Sprintf("%o.%o.%o.1", n, real_places, Abs(D));
end intrinsic;


intrinsic AmbientTypeLabel(AmbientType::Cat) -> MonStgElt
{ TODO }
     case AmbientType:
        when GLPlus_Type: return "sl";
        when SL_Type: return "gl";
    else
        error "Ambient type not supported.";
    end case;
end intrinsic;

intrinsic GammaTypeLabel(GammaType::MonStgElt) -> MonStgElt
{ TODO }
// strings for the time being
GAMMA_Type := "Gamma";
GAMMA_0_Type := "Gamma0";
GAMMA_1_Type := "Gamma1";
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
 F := Field(G);
 field_label := LMFDBLabel(F);
 level_label := LMFDBLabel(Level(G));
 Cl, mp := NarrowClassGroup(F);
 mpdet := IdealRepsMapDeterministic(F, mp);
 comp_label := LMFDBLabel(mpdet[ComponentIdeal(G) @@ mp]);
 ambient_label := AmbientTypeLabel(AmbientType(G));
 gamma_label := GammaTypeLabel(GammaType(G));
 return Join([field_label, level_label, comp_label, ambient_label, gamma_label], "-");
end intrinsic;
