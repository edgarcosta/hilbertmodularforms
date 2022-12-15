
intrinsic LMFDBLabel(F::FldNum) -> MonStgElt
 { LMFDB label for quadratic fields }
 n := Degree(F);
 require n eq 2: "only quadratic fields for now";
 D := Discriminant(Integers(F));
 real_places := D gt 0 select 2 else 0;
 return Sprintf("%o.%o.%o.1", n, real_places, Abs(D));
end intrinsic;


GammaTypeToLabel := AssociativeArray();
GammaTypeToLabel["Gamma"] := "f";
GammaTypeToLabel["Gamma_0"] := "0";
GammaTypeToLabel["Gamma_1"] := "1";


AmbientTypeToLabel := AssociativeArray();
AmbientTypeToLabel["GL"] := "gl";
AmbientTypeToLabel["SL"] := "sl";

intrinsic LMFDBLabel(G::GrpHilbert) -> MonStgElt
 {LMFDB label for the congruence subgroups associated to Hilbert modular forms}
 F := Field(G);
 field_label := LMFDBLabel(F);
 level_label := LMFDBLabel(Level(G));
 Cl, mp := NarrowClassGroup(F);
 mpdet := NarrowClassGroupRepsMapDeterministic(F, Cl, mp);
 comp_label := LMFDBLabel(mpdet[mp(comp)]);
 ambient_label := AmbientTypeToLabel[AmbientType(G)];
 gamma_label := GammaTypeToLabel[GammaType(G)];
 return Join("[field_label, level_label, comp_label, ambient_label, gamma_label]", "-");
end intrinsic;
