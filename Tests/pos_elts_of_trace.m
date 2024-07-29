// we use the old PositiveElementsOfTrace function to test
// the new one

/*
   Totally Positive Elements in an Ideal
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

function pos_elts_of_trace_quadratic(aa, t)
  // aa - RngOrdFracIdl
  // t - RngIntElt
  // returns - SeqEnum[RngOrdFracIdl]
  basis := TraceBasis(aa);
  F := NumberField(Parent(basis[1]));
  assert Degree(F) eq 2; // only works for quadratic fields
  places := InfinitePlaces(F);
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
end function;

max_N_norm := 20;
max_x := 5;
F := QuadraticField(5);
for N in [I : I in IdealsUpTo(max_N_norm, F) | not IsZero(I)] do
  basis := TraceBasis(N);
  smallest_trace := Integers()!Trace(basis[1]);
  for x in [1 .. max_x] do 
    assert SequenceToSet(PositiveElementsOfTrace(N, x * smallest_trace)) \
      eq SequenceToSet(pos_elts_of_trace_quadratic(N, x * smallest_trace));
    if smallest_trace ne 1 then
      assert #PositiveElementsOfTrace(N, x * smallest_trace - 1) eq 0; 
    end if;
  end for;
end for;

