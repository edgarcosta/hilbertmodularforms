function LatexElementOneLine(x)
  den := Denominator(x);
  num := den * x;
  if (den eq 1) then
    return Sprintf("%o", num);
  end if;
  return Sprintf("\\frac{%o}{%o}", num, den);
end function;

function FractionalIdealOneLine(I)
  ZF := Order(I);
  F := NumberField(ZF);
  if I eq 1*ZF then
    return "\\Z_F";
  end if;
  is_principal, gen := IsPrincipal(I);
  if is_principal then
    _, gen := IsNarrowlyPrincipal(I);
    return LatexElementOneLine(F!gen) * "\\Z_F";
  end if;
  gens := [LatexElementOneLine(F!g) : g in Generators(I)];
  s := Sprintf("\\left(%o", gens[1]);
  for g in gens[2..#gens] do
    s *:= Sprintf(", %o", g);
  end for;
  s *:= "\\right)";
  return s;
end function;

function figure1(frakb, B : scale := 0.9, max_grid := 12.0,
                            min_grid := -2.0, margin := 1.0, min_shadows := 3, radius := 0.05)
  output_lines := [];
  Append(~output_lines, "\\begin{figure}");
  Append(~output_lines, Sprintf("\\begin{tikzpicture}[scale=%.4o]",scale));
  Append(~output_lines, "%Vertices of Shintani cone");
  ZF := Order(frakb);
  F := NumberField(ZF);
  frakb_prime := Different(ZF)^(-1)*frakb;
  eps := F!TotallyPositiveUnitsGenerators(F)[1];
  v_eps := Sort(RealEmbeddings(eps));
  cone_coords := [Sqrt(B*v) : v in v_eps];
  Append(~output_lines, Sprintf("\\def\\xA{%.4o}",cone_coords[2]));
  Append(~output_lines, Sprintf("\\def\\yA{%.4o}",cone_coords[1]));
  // Here A and B are the right and left endpoints of the cone, respectively.
  Append(~output_lines, "\\draw node (A) at (\\xA, \\yA) {};");
  Append(~output_lines, "\\draw node[right] at (A) {$\\quad \\left(\\sqrt{Bv_1(\\eps)},\\sqrt{B/v_1(\\eps)}\\right)$};");
  Append(~output_lines, "\\draw node (B) at (\\yA, \\xA) {};");
  Append(~output_lines, "\\draw node[right] at (B) {$\\quad \\left(\\sqrt{B/v_1(\\eps)},\\sqrt{Bv_1(\\eps)}\\right)$};");
  Append(~output_lines, "%Fill");
  Append(~output_lines, "\\fill [blue!10] (0,0) -- (A.center) -- (\\xA, 0);");
  Append(~output_lines, "\\fill [blue!10] (0,0) -- (B.center) -- (0, \\xA);");
  Append(~output_lines, "\\fill [green!10] (0,0) -- (B.center)");
  Append(~output_lines, Sprintf("plot [domain=\\yA:\\xA] (\\x,%.4o/\\x)", B));
  Append(~output_lines, "-- (A.center) -- (0,0);");
  Append(~output_lines, "%Axes");
  // This was originally from (0,-1) !? Is there a reason to keep
  // the asymmetry?
  Append(~output_lines, Sprintf("\\draw [->] (0,%.4o) -- (0,%.4o);", min_grid, max_grid));
  Append(~output_lines, Sprintf("\\draw [->] (%.4o,0) -- (%.4o,0);", min_grid, max_grid));
  Append(~output_lines,"%Norm bound");
  Append(~output_lines, Sprintf("\\draw [domain=%.4o:%.4o] plot (\\x,%.4o/\\x);", B/max_grid, max_grid, B));
  Append(~output_lines, "%Shintani axes");
  Append(~output_lines, "\\draw (0,0) -- (A.center);");
  Append(~output_lines, Sprintf("\\draw [dashed] (A.center) -- (%.4o, %.4o);", max_grid, max_grid * v_eps[1]));
  Append(~output_lines, "\\draw (0,0) -- (B.center);");
  Append(~output_lines, Sprintf("\\draw [dashed] (B.center) -- (%.4o, %.4o);", max_grid * v_eps[1], max_grid));
  Append(~output_lines, "%Projections");
  Append(~output_lines, "\\draw [dashed] (A.center) -- (\\xA, 0);");
  Append(~output_lines, "\\draw [dashed] (B.center) -- (0, \\xA);");
  Append(~output_lines, "%Lattice points");
  // This was originally from (-2,-1.1) to (10.1, 9.9)
  // - allowing more from left to right than bottom up  !?
  min_lat := min_grid + margin;
  max_lat := max_grid - margin;
  Append(~output_lines, Sprintf("{\\clip (%.4o,%.4o) rectangle (%.4o,%.4o);",
				min_lat, min_lat, max_lat, max_lat));
  M := GradedRingOfHMFs(F,1);
  lat_pts := ElementsInABox(M, frakb_prime, min_lat, min_lat, max_lat, max_lat);
  for pt in lat_pts do
    real_pt := RealEmbeddings(pt);
    Append(~output_lines, Sprintf("\\def\\xx{{%.4o}}", real_pt[1]));
    Append(~output_lines, Sprintf("\\def\\yy{{%.4o}}", real_pt[2]));
    Append(~output_lines, Sprintf("\\draw[fill] ({\\xx},{\\yy}) circle (%.4o);",
				  radius));
  end for;
  Append(~output_lines, "}");
  Append(~output_lines, "%Draw three \"shadows\"");
  norms := {Norm(l) : l in lat_pts | Norm(l) le B};
  norm_desc := Reverse(Sort(SetToSequence(norms)));
  idx := 0;
  shadows := [];
  while #shadows lt min_shadows do
    idx +:= 1;
    n := norm_desc[idx];
    shadows cat:= [l : l in lat_pts | Norm(l) eq n and
		   Max(RealEmbeddings(l)) lt cone_coords[2]];
  end while;
  for pt in shadows do
    real_pt := RealEmbeddings(pt);
    Append(~output_lines, Sprintf("\\def\\xx{{%.4o}}", real_pt[1]));
    Append(~output_lines, Sprintf("\\def\\yy{{%.4o}}", real_pt[2]));
    Append(~output_lines, "\\draw [dashed] (\\xx,\\yy) -- (\\xx,0);");
    Append(~output_lines, "\\draw [dashed] (\\xx,\\yy) -- (0,\\yy);");
  end for;
  Append(~output_lines, "\\end{tikzpicture}");
  assert AbsoluteDegree(F) eq 2;
  assert Trace(F.1) eq 0;
  d := -Norm(F.1);
  AssignNames(~F, [Sprintf("\\sqrt{%o}", d)]);
  caption := "\\caption{The sets $\\FunDomain{\\frakb'}{B}$ and $\\FunDomShadow{\\frakb'}{B}$ for ";
  caption cat:= Sprintf("$F = \\Q(%o)$, $\\frakb = %o$ (so that $\\frakb' = %o$), and $B=%o$. ", 
                        F.1, FractionalIdealOneLine(frakb), FractionalIdealOneLine(frakb_prime), B);
  caption cat:= "The set $\\FunDomain{\\frakb'}{B}$ consists of lattice points in the green region, ";
  caption cat:= "and the set $\\FunDomShadow{\\frakb'}{B}$ consists of the points in $\\FunDomain{\\frakb'}{B}$ as well as the ";
  caption cat:= "points in the blue region.}";
  Append(~output_lines, caption);
  Append(~output_lines, "\\label{fig:shadow}");
  Append(~output_lines, "\\end{figure}");
  return Join(output_lines, "\n");
end function;

procedure write_figure1_to_file(fname, frakb, B : scale := 0.9,
				max_grid := 12.0, min_grid := -2.0,
				margin := 1.0, min_shadows := 3, radius := 0.05)
  figure := figure1(frakb, B : scale := scale, max_grid := max_grid,
		    min_grid := min_grid, margin := margin,
		    min_shadows := min_shadows, radius := radius);
  header := "% This file is auto-generated using the function figure1 in\n% ";
  ZF := Order(frakb);
  F := NumberField(ZF);
  assert AbsoluteDegree(F) eq 2;
  assert Trace(F.1) eq 0;
  d := -Norm(F.1);
  AssignNames(~F, [Sprintf("\\sqrt{%o}", d)]);
  header cat:= Sprintf("figures/figure1.m with frakb = %o and B = %o\n", FractionalIdealOneLine(frakb), B);
  header cat:= "% and parameters:\n% ";
  header cat:= Sprintf("scale = %.4o, max_grid = %.4o, min_grid = %.4o\n", scale, max_grid, min_grid);
  header cat:= "% ";
  header cat:= Sprintf("margin = %.4o, min_shadows = %o, radius = %.4o\n", margin, min_shadows, radius);
  Write(fname, header cat figure : Overwrite);
  return;
end procedure;
