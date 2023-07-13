// IO
intrinsic WriteGeometricInvariantsToRow(Gamma::GrpHilbert) -> MonStgElt
{Script for writing geometric invariants to data table row.
Format is label:[h^[2,0], h^[1,1]]:K^2:chi.}
  h2 := HodgeDiamond(Gamma)[3];
  return StripWhiteSpace(Join([
        LMFDBLabel(Gamma),
        //Sprint(KodairaDimension(Gamma)),
        Sprint(h2[1..2]),
        Sprint(K2(Gamma)),
        Sprint(ArithmeticGenus(Gamma))
  ], ":"));
end intrinsic;


elseq_to_postgres := func<x|ReplaceCharacter(ReplaceCharacter(Sprint(x), "[","{"), "]","}")>;
function EndsWith(s, x)
  if #x gt #s then return false; end if;
  return s[#s-#x+1..#s] eq x;
end function;
function handler_wrap(handler, x)
  _, type, fn := Explode(handler);
  s := StripWhiteSpace(Sprint(handler[3](x)));
  if EndsWith(type, "[]") then s := elseq_to_postgres(s); end if;
  return s;
end function;
id := func<x|x>;
// list of search cols
// <name, type, function, needs inds and lmfdb_index>
inv_column_handler := [*
  <"label", "text", LMFDBLabel>,
  <"field_label", "text", func<G|Split(LMFDBLabel(G), "-")[1]>>,
  <"component_label", "text", func<G|Split(LMFDBLabel(G), "-")[3]>>,
  <"gamma_type", "text", func<G|Split(LMFDBLabel(G), "-")[5]>>,
  <"group_type", "text", func<G|Split(LMFDBLabel(G), "-")[4]>>,
  <"level_label", "text", func<G|Split(LMFDBLabel(G), "-")[2]>>,
  <"level_gens", "bigint[]", func<G|[Eltseq(x): x in Generators(Level(G))]>>,
  <"comp_gens", "bigint[]", func<G|[Eltseq(x): x in Generators(ComponentIdeal(G))]>>,
  <"kodaira_dims", "integer[]", KodairaDimensionPossibilities>,
  <"K2", "integer", K2>,
  // chi -> holomorphic_euler_characteristic
  <"chi", "integer", ArithmeticGenus>,
  <"h11", "integer", func<G|HodgeDiamond(G)[3][2]>>,
  <"h20", "integer", func<G|HodgeDiamond(G)[3][1]>>,
  <"narrow_class_nb", "integer", func<G|NarrowClassNumber(BaseField(G))>>,
  <"level_norm", "integer", func<G|Norm(Level(G))>>,
  <"nb_cusps", "integer", NumberOfCusps>,
  <"field_discr", "integer", func<G|Discriminant(BaseField(G))>>,
  <"nb_ell", "integer", NumberOfEllipticPoints>,
  <"nb_ell2", "integer", func<G|NumberOfEllipticPoints(G,2)>>,
  <"nb_ell3", "integer", func<G|NumberOfEllipticPoints(G,3)>>,
  <"nb_ell4", "integer", func<G|NumberOfEllipticPoints(G,4)>>,
  <"nb_ell5", "integer", func<G|NumberOfEllipticPoints(G,5)>>,
  <"nb_ell6", "integer", func<G|NumberOfEllipticPoints(G,6)>>,
  <"len_cusp_res", "integer", LengthOfCuspResolutions>,
  <"len_ell_res", "integer", LengthOfEllipticPointResolutions>,
  <"len_res", "integer", LengthOfResolutions>,
  <"euler_nb", "integer", EulerNumber>,
  <"is_pp", "boolean", func<G|IsNarrowlyPrincipal(Different(Integers(BaseField(G))) * Component(G))>>
*];

intrinsic WriteHeader(handlers) -> MonStgElt
{Script for writing information about the surface to table row.}
  headers := [[col[1] : col in handlers]];
  headers cat:= [[col[2] : col in handlers]];

  return Join([Join([elt : elt in row], ":") : row in headers], "\n") cat "\n";
end intrinsic;

intrinsic WriteInvariantsHeader() -> MonStgElt
{Script for writing information about the surface to table row.}
  return WriteHeader(inv_column_handler);
end intrinsic;


intrinsic WriteInvariantsRow(Gamma::GrpHilbert) -> MonStgElt
{Script for writing information about the surface to table row.}
  return Join([handler_wrap(elt, Gamma) : elt in inv_column_handler], ":");
end intrinsic;

intrinsic WriteInvariantsRow(label::MonStgElt) -> MonStgElt
{Script for writing information about the surface to table row.}
  G := LMFDBCongruenceSubgroup(label);
  return WriteInvariantsRow(G);
end intrinsic;


elliptic_points_table := [*
  <"label", "text", func<x|x[1]>>,
  <"rotation_type", "integer[]", func<x|x[2]>>,
  <"nb", "integer", func<x|x[3]>>
*];

intrinsic WriteElllipticPointsHeader() -> MonStgElt
{Script for writing information about the surface to table row.}
  return WriteHeader(elliptic_points_table);
end intrinsic;

intrinsic WriteElllipticPointsRows(label::MonStgElt) -> MonStgElt
{Script for writing information about the elliptic points on the surface to table row.}
  G := LMFDBCongruenceSubgroup(label);
  return WriteElllipticPointsRows(G);
end intrinsic;


intrinsic WriteElllipticPointsRows(Gamma::GrpHilbert) -> MonStgElt
{Script for writing information about the elliptic points on the surface to table row.}
  C := CountEllipticPoints(Gamma);
  label := LMFDBLabel(Gamma);
  return Join([
          Join([handler_wrap(elt, <label, key[1], value>) : elt in inv_column_handler ], ":")
          : key->value in EllipticPointData(Gamma)
              ], "\n");
end intrinsic;


/*
intrinsic WriteLMFDBRow(Gamma::GrpHilbert) -> MonStgElt
{Script for writing information about the surface to table row.
Format is
label:field_label:field_discr:narrow_class_nb:level_label:level_norm:component_label:is_pp:group_type:gamma_type:h20:h11:K2:chi:number_of_cusps:kposs
where is_pp is true iff component is the inverse different of the quadratic field.}
    F_label, N_label, b_label, group_type, gamma_type := Explode(Split(LMFDBLabel(Gamma), "-"));
    F := BaseField(Gamma);
    N := Level(Gamma);
    b := ComponentIdeal(Gamma);
    h2 := HodgeDiamond(Gamma)[3];
    is_pp := IsNarrowlyPrincipal(Different(Integers(F)) * Component(Gamma));
    Ngens := [Eltseq(x): x in Generators(N)];
    bgens := [Eltseq(x): x in Generators(b)];
    res := StripWhiteSpace(Join([Sprint(elt) : elt in [*
      LMFDBLabel(Gamma),
      F_label,
      b_label,
      gamma_type,
      group_type,
      N_label,
      Ngens,
      bgens,
      KodairaDimensionPossibilities(Gamma),
      K2(Gamma),
      ArithmeticGenus(Gamma),
      h2[1],
      h2[2],
      NarrowClassNumber(F),
      Norm(N),
      NumberOfCusps(Gamma),
      Discriminant(F),
      NumberOfEllipticPoints(Gamma),
      NumberOfEllipticPoints(Gamma, 2),
      NumberOfEllipticPoints(Gamma, 3),
      NumberOfEllipticPoints(Gamma, 4),
      NumberOfEllipticPoints(Gamma, 5),
      NumberOfEllipticPoints(Gamma, 6),
      LengthOfCuspResolutions(Gamma),
      LengthOfEllipticPointResolutions(Gamma),
      LengthOfResolutions(Gamma),
      EulerNumber(Gamma),
      is_pp
      *]], ":"));
end intrinsic;
*/

