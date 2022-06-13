declare type RngMPolGrd [RngMPolGrdElt];
declare attributes RngMPolGrd:
		   BaseRing,
	Generators,
	MonomialOrder,
	Names,
	Rank;

declare attributes RngMPolGrdElt:
		   Coeffs,
	Degree,
	Monomials,
	Parent;

////////// RngMPolGrd fundamental intrinsics //////////

intrinsic Print(R::RngMPolGrd, level::MonStgElt)
  {}
  if level in ["Default", "Minimal", "Maximal"] then
    printf "Graded Polynomial ring of rank %o over %o\n", Rank(R), BaseRing(R);
    printf "Order: %o with weights %o\n", MonomialOrder(R)[1], MonomialOrder(R)[2];
    printf "Variables: ";
    genseq := GeneratorsSequence(R);
    for g in genseq[1..#genseq-1] do
	printf "%o, ", g;
    end for;
    printf "%o\n", genseq[#genseq];
    printf "Variable weights: [";
    for g in genseq[1..#genseq-1] do
	printf "%o, ", Degree(g);
    end for;
    printf "%o]", Degree(genseq[#genseq]);
  elif level eq "Magma" then
      error "not implemented!";
  else
      error "not a valid printing level.";
  end if;
end intrinsic;

function createGradedMonomial(R, vec, deg)
    mon := New(RngMPolGrdElt);
    mon`Parent := R;
    mon`Monomials := AssociativeArray();
    mon`Monomials[vec] := BaseRing(R)!1;
    mon`Degree := deg;
    return mon;
end function;

intrinsic AssignNames(~R::RngMPolGrd, names::SeqEnum[MonStgElt])
{}
  R`Names := names;
end intrinsic;

intrinsic Name(R::RngMPolGrd, i::RngIntElt) -> RngMPolGrdElt
{}
  return R.i;
end intrinsic;

intrinsic NumberOfNames(R::RngMPolGrd) -> RngIntElt
{}
  return Rank(R);
end intrinsic;

intrinsic GradedPolynomialRing(R::Rng, G::SeqEnum[GrpElt], T::Tup) -> RngMPolGrd
{Create the graded multivariate polynomial ring over R in #G variables with the given grading G on the variables and with the order described by tuple T (matching what is returned by MonomialOrder).}
  Rpoly := New(RngMPolGrd);
  Rpoly`BaseRing := R;
  Rpoly`Rank := #G;
  Rpoly`MonomialOrder := T;
  Rpoly`Names := [];
  e := [[0 : j in [1..#G]] : i in [1..#G]];
  for i in [1..#G] do
      e[i][i] := 1;
  end for;
  Rpoly`Generators := [ createGradedMonomial(Rpoly, e[i], G[i]) : i in [1..#G]];
  return Rpoly;
end intrinsic;

intrinsic '.'(R::RngMPolGrd, i::RngIntElt) -> RngMPolGrdElt
{}
  return R`Generators[i];	     
end intrinsic;

intrinsic 'eq'(R1::RngMPolGrd, R2::RngMPolGrd) -> BoolElt
{}
  if (BaseRing(R1) ne BaseRing(R2)) then return false; end if;
  if (Rank(R1) ne Rank(R2)) then return false; end if;
  if (MonomialOrder(R1) ne MonomialOrder(R2)) then return false; end if;
  return true;
end intrinsic;

intrinsic BaseRing(R::RngMPolGrd) -> Rng
{}
  return R`BaseRing;
end intrinsic;

intrinsic GeneratorsSequence(R::RngMPolGrd) -> SeqEnum[RngMPolGrdElt]
{}
  return [R.i : i in [1..Rank(R)]];
end intrinsic;

intrinsic MonomialOrder(R::RngMPolGrd) -> Tup
{}
  return R`MonomialOrder;
end intrinsic;

intrinsic Ngens(R::RngMPolGrd) -> RngIntElt
{}
  return R`Rank;
end intrinsic;

intrinsic Rank(R::RngMPolGrd) -> RngIntElt
{}
  return R`Rank;
end intrinsic;

////////// RngMPolGrdElt fundamental intrinsics //////////

function printMonomial(exponents : names := [])
    out_str := "";
    if IsEmpty(names) then
	names := [Sprintf("$.%o", i) : i in [1..#exponents]];
    end if;
    for i->e in exponents do
	if e gt 0 then
	    if #out_str gt 0 then
		out_str cat:= "*";
	    end if;
	    if e eq 1 then 
		out_str cat:= names[i];
	    else
		out_str cat:= names[i] cat Sprintf("^%o", e);
	    end if;
	end if;
    end for;
    return out_str;
end function;

intrinsic Print(f::RngMPolGrdElt, level::MonStgElt)
  {}
  if level in ["Default", "Minimal", "Maximal"] then
      out_str := "";
      for mon in Keys(f`Monomials) do
	  coeff := f`Monomials[mon];
	  if coeff ne 0 then
	      if (#out_str gt 0) then
		  if (coeff gt 0) then
		      out_str cat:= " + ";
		  else
		      out_str cat:= " - ";
		  end if;
	      end if;
	      if (coeff ne 1) and (coeff ne -1) then
		  if (coeff gt 0) then
		      out_str cat:= Sprintf("%o*", coeff);
		  else
		      out_str cat:= Sprintf("%o*", -coeff);
		  end if;
	      end if;
	      mon_str := printMonomial(mon : names := Parent(f)`Names);
	      out_str cat:= mon_str;
	  end if;
      end for;
      printf "%o", out_str;
  elif level eq "Magma" then
      error "not implemented!";
  else
      error "not a valid printing level.";
  end if;
end intrinsic;

intrinsic Degree(f::RngMPolGrdElt) -> GrpElt
{}
  return f`Degree;
end intrinsic;

intrinsic Parent(f::RngMPolGrdElt) -> GrpElt
{}
  return f`Parent;
end intrinsic;

intrinsic '+'(f::RngMPolGrdElt, g::RngMPolGrdElt) -> RngMPolGrdElt
{}
  require Parent(f) eq Parent(g) : "Polynomials must be in the same ring.";
  require Degree(f) eq Degree(g) : "Can only add polynomials with the same degree.";

  h := New(RngMPolGrdElt);
  h`Parent := Parent(f);
  h`Monomials := AssociativeArray();
  for mon in (Keys(f`Monomials) join Keys(g`Monomials)) do
      is_def_f, f_val := IsDefined(f`Monomials, mon);
      is_def_g, g_val := IsDefined(f`Monomials, mon);
      h`Monomials[mon] := (is_def_f select f_val else 0) + (is_def_g select g_val else 0);
  end for;
    
  h`Degree := f`Degree;
  return h;
end intrinsic;

intrinsic '*'(f::RngMPolGrdElt, g::RngMPolGrdElt) -> RngMPolGrdElt
{}
  require Parent(f) eq Parent(g) : "Polynomials must be in the same ring.";

  h := New(RngMPolGrdElt);
  h`Parent := Parent(f);
  h`Monomials := AssociativeArray();
  for mon_f in Keys(f`Monomials) do
      for mon_g in Keys(g`Monomials) do
	  mon := [mon_f[i] + mon_g[i] : i in [1..#mon_f]];
	  is_def, val := IsDefined(h`Monomials, mon);
	  h`Monomials[mon] := (is_def select val else 0) + f`Monomials[mon_f] * g`Monomials[mon_g];
      end for;
  end for;
    
  h`Degree := f`Degree + g`Degree;
  return h;
end intrinsic;
