///// Shintani Algorithms + Enumerations of Totally positive elements in ideals /////////

intrinsic EmbedNumberFieldElement(nu::FldNumElt : Precision := 100) -> SeqEnum
  {}
  F := Parent(nu);
  return [Evaluate(nu, place : Precision := Precision) : place in InfinitePlaces(F)];
end intrinsic;

intrinsic EmbedNumberFieldElement(nu::RngElt : Precision := 100) -> SeqEnum
  {}
  R := Parent(nu);
  F := NumberField(R);
  return EmbedNumberFieldElement(F!nu : Precision := Precision);
end intrinsic;

intrinsic Slope(alpha::RngElt : Precision := 100) -> FldReElt
  { Input:  alpha, an element of ZF for F a totally real quadratic number field
    Output: The "slope" defined by alpha: sigma_2(alpha)/sigma_1(alpha) where
    sigma_i is the ith embedding of F}
  embed := EmbedNumberFieldElement(alpha : Precision := Precision);
  return embed[2]/embed[1];
end intrinsic;

intrinsic DistanceSquared(L::SeqEnum) -> Any
  {}
  return &+[Abs(el)^2 : el in L];
end intrinsic;

// Rearranges the basis for an ideal so that the second basis vector has trace 0
intrinsic TraceBasis(aa::RngOrdFracIdl) -> SeqEnum
  {Given a fractional ideal aa, returns a basis (a,b) in Smith normal form
   where Trace(a) = n > 0 and Trace(b) = 0}

  // Preliminaries
  B := Basis(aa);
  ZF := Parent(B[2]);
  places := InfinitePlaces(NumberField(ZF));

  // Change of basis
  trMat := Matrix([[Integers()!Trace(B[i])] : i in [1..#B]]);
  _, Q := HermiteForm(trMat);
  B := Eltseq(Vector(B)*Transpose(ChangeRing(Q,ZF)));
  assert Trace(B[1]) gt 0;
  assert Trace(B[2]) eq 0;
  // Orienting B
  if Evaluate(B[2], places[2]) lt 0 then
    B := [B[1], -B[2]];
  end if;
  return B;
end intrinsic;

///////////////////////////////////////////////////
//                                               //
//   Enumeration of Totally Positive elements    //
//                                               //
///////////////////////////////////////////////////

/*
// Totally Positive Elements in an Ideal
   From a basis {a,b} for the ideal bb where
     Tr(a) = n and Tr(b) = 0.
   Elements in ideal will look like xa + yb where x,y in ZZ
   and have embedding xa_1 + yb_1 and xa_2 + yb_2.
   All totally positive elements of given trace t will satisfy
   1)    t = Tr(xa+yb)    <=>   t = xn
   2)    xa+yb totally positive       <=>   y > -x*a_1/b_1   and  y > -x*a_2/b_2
   Eq 1) determines the value for x,
     and Eq 2) allows us to loop over values of y
*/
intrinsic PositiveElementsOfTrace(aa::RngOrdFracIdl, t::RngIntElt) -> SeqEnum[RngOrdFracIdl]
  {Given aa a fractional ideal and t a nonnegative integer,
   returns the totally positive elements of aa with trace t.}
  basis := TraceBasis(aa);
  places := InfinitePlaces(NumberField(Parent(basis[1])));
  smallestTrace := Integers()!Trace(basis[1]);
  T := [];
  if t mod smallestTrace eq 0 then
    x := t div smallestTrace;
    a_1 := Evaluate(basis[1],places[1]);
    a_2 := Evaluate(basis[1],places[2]);
    b_1 := Evaluate(basis[2],places[1]);
    b_2 := Evaluate(basis[2],places[2]);
    assert b_1 lt 0 and b_2 gt 0; // if this assumption changes, the inequalities get swapped
    // at place 2, x*a2 + y*b2 >= 0 => y >= -x*a2/b2
    lower_bnd := Ceiling(-x*a_2/b_2);
    // at place 1, x*a1 + y*b1 >= 0 => y <= -x*a1/b1
    upper_bnd := Floor(-x*a_1/b_1);
    for y in [lower_bnd .. upper_bnd] do
      Append(~T, x*basis[1]+y*basis[2]);
    end for;
  end if;
  return T;
end intrinsic;

intrinsic ElementsInABox(M::ModFrmHilDGRng, aa::RngOrdFracIdl,
                         XLBound::Any, YLBound::Any, XUBound::Any, YUBound::Any) -> SeqEnum
  {Enumerates all elements c in aa with XLBound <= c_1 <= XUBound and  YLBound <= c_2 <= YUBound}

  for bnd in [XUBound, YUBound, XLBound, YLBound] do
    require ISA(Type(bnd),FldReElt) : "Bounds must be coercible to real numbers";
  end for;
  basis := TraceBasis(aa);
  F := BaseField(M);
  ZF := Integers(M);
  places := Places(M);

  //if Evaluate(basis[2],places[1]) lt 0 then
  //  basis := [basis[1], -basis[2]];
  //end if;


  // Precomputationss
  a_1 := Evaluate(basis[1], places[1]);
  a_2 := Evaluate(basis[1], places[2]);
  b_1 := Evaluate(basis[2], places[1]);
  b_2 := Evaluate(basis[2], places[2]);
  assert b_1 lt 0 and b_2 gt 0; // if this assumption changes, the inequalities get swapped

  // List of all Elements
  T := [];
  trLBound := Ceiling(XLBound+YLBound);
  trUBound := Floor(XUBound+YUBound);
  for i in [trLBound..trUBound] do
    // at place 1, i*a2 + j*b2 <= XUBound => j >= (XUBound -i*a1)/b1
    // at place 2, i*a2 + j*b2 >= YLBound => j >= (YLBound -i*a2)/b2
    lBound := Ceiling(Max((XUBound-i*a_1)/b_1, (YLBound-i*a_2)/b_2));
    uBound := Floor(Min((XLBound-i*a_1)/b_1, (YUBound-i*a_2)/b_2));
    for j in [lBound..uBound] do
      Append(~T, i*basis[1] + j*basis[2]);
    end for;
  end for;

  return T;
end intrinsic;


///////////////////////////////////////////////////
//                                               //
//          Shintani Domain algorithms           //
//                                               //
///////////////////////////////////////////////////


// Helper Functions
// Returns the slopes of the upper and lower walls for the Shintani Domain
intrinsic ShintaniWalls(ZF::RngOrd) -> Any
  {returns lower and upper walls of the Shintani domain}
  require Degree(ZF) eq 2: "only implemented for quadratic fields";
  D := Discriminant(ZF);
  F := NumberField(ZF);
  places := InfinitePlaces(F);
  eps := FundamentalUnitTotPos(F);
  eps1 := Evaluate(eps, places[1]);
  eps2 := Evaluate(eps, places[2]);

  return Sqrt(eps1/eps2), Sqrt(eps2/eps1);
end intrinsic;


// Elements of the Shintani domain with trace t
/* Idea: We compute a basis a,b for the ideal aa where Tr(a) = n > 0 and Tr(b) = 0.
   Elements in ideal will look like xa+yb where x,y in ZZ and have embedding
      xa_1 + yb_1 and xa_2 + yb_2.
   All totally positive elements of given trace t will satisfy
   1) t = Tr(xa+yb)    <=>   t = xn
   2) C_1 < (xa_1+yb_1)/(xa_2+yb_2) < C_2    <=>
      (C_1*x*a_2-x*a_1)/(b_1-C_1*b_2) < y < (C_2*x*a_2-x*a_1)/(b_1-C_2*b_2)
   where C1 and C2 are the slope bounds on the Shintani domain.
   Eq 1) determines the value for x while
   Eq 2) allows us to loop over values of y.
*/
intrinsic ShintaniRepsOfTrace(aa::RngOrdFracIdl, t::RngIntElt) -> SeqEnum[RngOrdFracIdl]
  {Given aa a fractional ideal, t a trace, returns the totally positive elements
   of aa in the balanced Shintani cone with trace t.}

  basis := TraceBasis(aa);
  F := NumberField(Parent(basis[1]));
  require Degree(F) eq 2: "this is hardcoded for quadratic fields";
  ZF := Integers(F);
  places := InfinitePlaces(F);

  if t eq 0 then
    return [ZF!0];
  else

    smallestTrace := Integers()!Trace(basis[1]);
    T := [];
    if t mod smallestTrace eq 0 then
      x := t div smallestTrace;
      C1,C2 := ShintaniWalls(ZF);
      a1 := Evaluate(basis[1], places[1]);
      b1 := Evaluate(basis[2], places[1]);
      a2 := Evaluate(basis[1], places[2]);
      b2 := Evaluate(basis[2], places[2]);

      lowerbnd := (C2*x*a2-x*a1)/(b1-C2*b2);
      upperbnd := (C1*x*a2-x*a1)/(b1-C1*b2);
      // Magma has some extreme problems with .999999999 /= 1.
      // That is why this is defined in a terrible manner.
      // It removes points that lie on the upper wall.
      prec := Precision(lowerbnd);
      if Abs(Round(lowerbnd) - lowerbnd) lt 10^(-prec/2) then
        lowerbnd := Round(lowerbnd);
      else
        lowerbnd := Ceiling(lowerbnd);
      end if;
      if Abs(Round(upperbnd) - upperbnd) lt 10^(-prec/2) then
        upperbnd := Round(upperbnd)-1;
      else
        upperbnd := Floor(upperbnd);
      end if;
      for y in [lowerbnd .. upperbnd] do
        Append(~T, x*basis[1]+y*basis[2]);
      end for;
    end if;
    return T;
  end if;
end intrinsic;


///////////////////////////////////////////////////
//                                               //
//          Shintani Reduction Algorithms        //
//                                               //
///////////////////////////////////////////////////

// Shintani reduction algorithm
// Use this function: it first does a lookup to see if already in the
// Shintani cone, else it seeks to minimize the trace
intrinsic ReduceShintani(M::ModFrmHilDGRng,  bb::RngOrdFracIdl, nu::RngElt) -> RngOrdElt
  {Reduce the element nu in component labelled bb.}
  // assert Parent(nu) eq Integers(M); Edgar: Why?
  if nu in ShintaniReps(M)[bb] then
    // Is reduced
    return nu, 1;
  else
    newnu, epsilon := Explode(ReduceShintaniMinimizeTrace(nu));
    return newnu, epsilon; // pass the unit as optional
  end if;
end intrinsic;

// Shintani reduction algorithm (workhorse)
intrinsic ReduceShintaniMinimizeTrace(nu::RngElt) -> Tup
  {Reduce the element nu to the Shintani domain.}

  if nu eq 0 then
    return <Parent(nu)!0, 1>;
  end if;

  // Preliminaries
  ZF := Parent(nu);
  F := NumberField(ZF);
  // Asserts
  require IsTotallyPositive(nu): "nu must be totally positive";
  require Degree(F) eq 2: "Shintani domains only implemented for quadratic fields";

  // Fundamental unit
  eps := FundamentalUnitTotPos(F);

  eps_RR := [Evaluate(eps,pl) : pl in InfinitePlaces(F)];
  slope_eps := Slope(eps);
  slope_nu := Slope(nu);

  RR := RealField(100);
  ratio := RR!(1/2)*Log(RR!slope_nu)/Log(RR!eps_RR[1]);
  ratio_ceiling := Ceiling(ratio);
  ratio_floor := Floor(ratio);
  nu_ceiling := eps^ratio_ceiling*nu;
  nu_floor := eps^ratio_floor*nu;
  slope_nu_ceiling := Slope(nu_ceiling);
  slope_nu_floor := Slope(nu_floor);
  slopes := [slope_nu_floor, slope_nu_ceiling];
  nus := [nu_floor, nu_ceiling];
  epses := [eps^ratio_floor, eps^ratio_ceiling];
  ParallelSort(~slopes, ~nus);
  ParallelSort(~slopes, ~epses);
  if IsShintaniReduced(nus[1]) then
    return <nus[1], epses[1]>;
  else
    assert IsShintaniReduced(nus[2]);
    return <nus[2], epses[2]>;
  end if;
end intrinsic;

intrinsic ReduceShintaniMinimizeDistance(nu::FldNumElt : Precision := 100) -> Tup
  {Find the multiple of nu by a totally positive unit that is closest to the origin.}

  F := Parent(nu);
  require Degree(F) eq 2: "Shintani domains only implemented for quadratic fields";
  if nu eq 0 then
    return <Parent(nu)!0, 1>;
  end if;
  eps := FundamentalUnitTotPos(F);
  eps_RR := EmbedNumberFieldElement(eps : Precision := Precision);
  nu_RR := EmbedNumberFieldElement(nu : Precision := Precision);
  r := 1/(2*(Log(eps_RR[1])-Log(eps_RR[2])))*(Log(-(nu_RR[2]^2/nu_RR[1]^2)*(Log(eps_RR[2])/Log(eps_RR[1]))));
  r_floor := Floor(r);
  r_ceiling := Ceiling(r);
  rs := [r_floor, r_ceiling];
  nus_min := [eps^r_floor*nu, eps^r_ceiling*nu];
  dists := [];
  for el in nus_min do
    embed := EmbedNumberFieldElement(el : Precision := Precision);
    Append(~dists, embed[1]^2 + embed[2]^2);
  end for;
  _, ind := Min(dists);
  return nus_min[ind], eps^rs[ind];
end intrinsic;

intrinsic ReduceShintaniMinimizeDistance(nu::RngElt : Precision := 100) -> Tup
  {}
  R := Parent(nu);
  F := NumberField(R);
  return ReduceShintaniMinimizeDistance(F!nu : Precision := Precision);
end intrinsic;

// Test if an element is Shintani reduced
intrinsic IsShintaniReduced(nu::RngElt) -> BoolElt
  {Tests if the totally nonnegative element nu is Shintani reduced.}

  // zero is Shintani Reduced
  if nu eq Parent(nu)!0 then
    return true;
  end if;

  // wall1 < wall2
  wall1, wall2 := ShintaniWalls(Integers(Parent(nu)));
  slope := Slope(nu);
  prec := Precision(Parent(slope));

  // walls with fuzz
  if (wall1-10^(-prec/2) le slope) and (slope le wall2+10^(-prec/2)) then
    return true;
  else
    return false;
  end if;
end intrinsic;



/////////////////////// Conversion Functions /////////////////////


// Conversion : Shintani elements < = > Ideals
// Converts pairs (bb,nu) <-> (bb,nn) based on the set of representatives bb for Cl^+(F)
intrinsic IdealToShintaniRepresentative(M::ModFrmHilDGRng, bb::RngOrdIdl, nn::RngOrdIdl) -> RngOrdElt
  {Takes a representative [bb] in Cl^+(F) and an integral ideal nn in ZF
   with [nn] = [bbp^(-1)] where bbp = dd_F*bb^-1 and returns Shintani
   representative (nu) = nn*bbp = nn*bb*dd_F^(-1), dealing with nn = (0).}

  if IsZero(nn) then
    return 0;
  end if;

  if not IsDefined(M`IdealShitaniReps[bb], nn) then
    F := BaseField(M);
    ZF := Integers(M);
    // dd := Different(ZF);
    // bbp := bb*(dd)^-1;
    bbp := NarrowClassGroupRepsToIdealDual(M)[bb];

    mp := NarrowClassGroupMap(M);
    require IsIdentity((nn*bbp)@@mp): "The ideals nn and bb must be inverses in CL+(F)";
    bool, gen := IsNarrowlyPrincipal(nn*bbp);
    assert bool;
    M`IdealShitaniReps[bb][nn] := ReduceShintani(M, bb, gen);
  end if;
  return M`IdealShitaniReps[bb][nn];
end intrinsic;

// Conversion : Shintani elements < = > Ideals
// Converts nu <-> nn, without needing bb as input
intrinsic IdealToShintaniRepresentative(M::ModFrmHilDGRng, nn::RngOrdIdl) -> RngOrdElt
  {Takes a representative [bb] in Cl^+(F) and an integral ideal n in ZF with
   [n] = [bb^(-1)] and returns Shintani representative (nu) = n*bb}
  F := BaseField(M);
  mp := NarrowClassGroupMap(M);
  bbp := mp(-(nn @@ mp)); // bb' is inverse of nn in narrow class group
  bool, gen := IsNarrowlyPrincipal(nn*bbp);
  assert bool;
  // This is hardcoded for quadratic Fields.
  require Degree(BaseField(M)) eq 2: "This function is hardcoded for quadratic fields.";
  return ReduceShintaniMinimizeTrace(gen)[1]; // we don't care about the unit
end intrinsic;

// Converts nus to nns
intrinsic ShintaniRepresentativeToIdeal(M::ModFrmHilDGRng, bb::RngOrdIdl, nu::RngElt) -> RngOrdIdl
  {Takes a representative [bb^(-1)] in Cl^+(F) and a nu in bb_+ and returns the
   integral ideal n = bb^(-1)*(nu) in ZF,
   and caches this into M`ShintaniRepsIdeal
  }
  if not IsDefined(M`ShintaniRepsIdeal[bb], nu) then
    bbp := NarrowClassGroupRepsToIdealDual(M)[bb];
    M`ShintaniRepsIdeal[bb][nu] := NicefyIdeal(nu*bbp^(-1));
  end if;
  return M`ShintaniRepsIdeal[bb][nu];
end intrinsic;


/* UNUSED
intrinsic PopulateShintaniRepsIdeal(M::ModFrmHilDGRng, bb::RngOrdFracIdl, nus::SetEnum[RngOrdElt])
 {populates ShintaniRepsIdeal[bb][nu] for nu in nus}
  bbinv := bb^(-1);
  for nu in nus diff Keys(M`ShintaniRepsIdeal[bb]) do
    // See ShintaniRepresentativeToIdeal
    M`ShintaniRepsIdeal[bb][nu] := NicefyIdeal(nu*bbinv);
  end for;
end intrinsic;
*/
