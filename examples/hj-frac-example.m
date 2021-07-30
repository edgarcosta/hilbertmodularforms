
// Maybe make PeriodBound depend on precision of input to avoid false non-repeating
// Currently only works for elements of precision field...best solution is probably to make intrinsic and overload...
// Gives wrong output when w_new is just slightly larger than an integer...try RealField(100)!(7/3) for example
function HJContinuedFraction(w0 : PeriodBound := 100, Epsilon := 0)
  // Input: Real number w0
  // Output: Two lists, the first containing the preperiodic portion and the second containing the repeating portion of the HJ continued fraction
  //         a boolean, true if the continued fraction repeats or terminates
  prec := Precision(Parent(w0));
  if Epsilon eq 0 then
    Epsilon := 10^(-prec/2);
  end if;
  eps := Epsilon;
  ws := [w0];
  b0 := Ceiling(w0);
  bs := [b0];
  zero_bool := false;
  rep_bool := false;
  i := 1;
  while (i le PeriodBound) and (not zero_bool) and (not rep_bool) do
    //printf "i = %o\n", i;
    diff_i := bs[i] - ws[i];
    //printf "diff_i = %o\n", diff_i;
    if Abs(diff_i) lt eps then
      zero_bool := true;
    else
      w_new := 1/diff_i; // this might exacerbate round-off errors
      //see https://sites.millersville.edu/bikenaga/number-theory/periodic-continued-fractions/periodic-continued-fractions.html
      //printf "w_new = %o\n", w_new;
      // check if remainder w_new already appeared in ws, which means that expansion is periodic
      j := 1;
      while j le #ws do
        if Abs(w_new - ws[j]) lt eps then
          rep_bool := true;
          rep_ind := j;
        end if;
        j := j + 1;
      end while;
      if (not rep_bool) and (not zero_bool) then
        Append(~ws, w_new);
        b_new := Ceiling(w_new);
        Append(~bs, b_new);
      end if;
    end if;
    i := i + 1;
  end while;
  printf "bs = %o\n", bs;
  // now return the appropriate lists
  if zero_bool then
    return bs, [], true;
  elif rep_bool then
    print "periodic continued fraction";
    head := bs[1..(rep_ind - 1)];
    tail := bs[rep_ind..#bs];
    return head, tail, true;
  else
    print "non-periodic continued fraction";
    return bs, [], false;
  end if;
end function;

function HJContinuedFractionToReal(bs : prec := 30)
  K := RealField(prec);
  cs := Reverse(bs);
  x := K!cs[1];
  for i := 2 to #cs do
    x := cs[i] - 1/x;
  end for;
  return x;
end function;

function PeriodicHJContinuedFractionToReal(head, tail : prec := 30, rep := 30)
  RR := RealField(prec);
  bs := head;
  for i := 1 to rep do
   bs := bs cat tail;
  end for;
  return HJContinuedFractionToReal(bs : prec := prec);
end function;

function VerifyExactHJContinuedFraction(a : Precision := 30, PeriodBound := 100)
  F<r> := Parent(a);
  assert (Degree(F) eq 2) and (IsTotallyReal(F));
  vs := InfinitePlaces(F);
  evs := [Evaluate(a, v : Precision := Precision) : v in vs];
  eq_bool := true;
  for ev in evs do
    head, tail, per_bool := HJContinuedFraction(ev : PeriodBound := PeriodBound);
    assert per_bool;
    y := a;
    for el in head do
      y := -1/(y-el);
    end for;
    printf "LHS y = %o\n", y;
    //y2 := a;
    y2 := y;
    cs := Reverse(tail);
    for i := 1 to #cs do
      y2 := cs[i] - 1/y2;
    end for;
    printf "RHS y = %o\n", y2;
    eq_bool and:= (y eq y2);
    assert y eq y2;
  end for;
  return eq_bool;
end function;

/*
    if diff_i ne 0 then
      w_new := 1/diff_i;
      j := 1;
      while j le #ws do
        if Abs(w_new - ws[j]) lt eps then
          rep_bool := true;
          rep_ind := j;
        end if;
        j := j+1;
      end while;
      if w_new in ws then // probably need to make this a "numerically" in with a precision parameter...
        
      else
        Append(~ws, w_new);
        b_new := Ceiling(w_new);
        Append(~bs, b_new);
      end if;
    else
      zero_bool := true;
    end if;
    i := i + 1;
  end while;
  if zero_bool then
    return bs, [], true;
  elif rep_bool then
    head := bs[1..(rep_ind - 1)];
    tail := bs[rep_ind..#bs];
    return head, tail, true;
  else
    return bs, [], false;
  end if;
end function;
*/

/*
// computing H-J continued fraction
//w0 := (3+Sqrt(5))/2;
w0 := 7/3;
//w0 := Sqrt(5);
ws := [w0];
b0 := Ceiling(w0);
bs := [b0];
for i := 1 to 20 do
  printf "i = %o\n", i;
  diff_i := bs[i] - ws[i];
  printf "diff_i := %o\n", diff_i;
  if diff_i ne 0 then
    w_new := 1/diff_i;
    Append(~ws, w_new);
    b_new := Ceiling(w_new);
    Append(~bs, b_new);
  else
    break;
  end if;
end for;

// converting H-J continued fraction back to decimal
K := Parent(w0);
cs := Reverse(bs);
xs := [K!cs[1]];
for i := 2 to #cs do
  x_new := cs[i] - 1/xs[i-1];
  Append(~xs, x_new);
end for;
*/

