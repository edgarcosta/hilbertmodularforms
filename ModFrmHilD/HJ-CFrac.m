// May give wrong output when w_new is just slightly larger than an integer; e.g., try RealField(100)!(7/3)
intrinsic HJContinuedFraction(w0 : PeriodBound := 100, Epsilon := -1) -> Any
  {Given a real number w0, return two lists, the first containing the preperiodic portion and the second containing the repeating portion of the HJ continued fraction, and a boolean, true if the continued fraction repeats or terminates}
  prec := Precision(Parent(w0));
  if Epsilon eq -1 then
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
end intrinsic;

intrinsic HJContinuedFractionToReal(bs : prec := 30) -> FldReElt
  {Given a list of integers, return the corresponding HJ continued fraction.}
  K := RealField(prec);
  cs := Reverse(bs);
  x := K!cs[1];
  for i := 2 to #cs do
    x := cs[i] - 1/x;
  end for;
  return x;
end intrinsic;

intrinsic PeriodicHJContinuedFractionToReal(head, tail : prec := 30, rep := 30) -> FldReElt
  {Given two lists of integers, the first containing the non-periodic part, and the second containing the periodic part, return the corresponding HJ continued fraction.}
  RR := RealField(prec);
  bs := head;
  for i := 1 to rep do
   bs := bs cat tail;
  end for;
  return HJContinuedFractionToReal(bs : prec := prec);
end intrinsic;

intrinsic VerifyExactHJContinuedFraction(a : Precision := 30, PeriodBound := 100) -> BoolElt
  {Given an element of a totally real number field of degree at most 2, verify that the periodic HJ continued fractions compute by HJContinuedFraction are correct.}
  F<r> := Parent(a);
  assert (Degree(F) le 2) and (IsTotallyReal(F));
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
end intrinsic;


intrinsic CeilingOfSquareRoot(n:: RngIntElt, b:: RngIntElt) -> RngIntElt
{Given a nonnegative integer n, compute the ceiling of sign(b) * sqrt(n)}
    if (n eq 0) then
	return 0;
    end if;
    //Is n a perfect square?
    x, y := SquareFree(n);
    y := Sign(b) * y;
    //If not, then compute ceiling of square root using sufficient real precision
    if (x ne 1) then
	prec := Ceiling(Log(n)/Log(10)) + 10;
	R := RealField(prec);
	y := Sign(b) * SquareRoot(R ! n);
	y := Ceiling(y);
    end if;    
    return y;
end intrinsic;

intrinsic UpperIntegerPart(w:: FldQuadElt) -> RngIntElt
{Compute the ceiling of w seen as a real number, assuming F.1 is positive}
    F := Parent(w);
    den := Denominator(w);
    seq := ElementToSequence(den * w); //Coefficients of den*w in canonical basis
    a := seq[1];
    b := seq[2];
    x := (b*F.1)^2;
    res := a + CeilingOfSquareRoot(Integers() ! x, Integers() ! b);
    return Ceiling(res/den);
end intrinsic;

intrinsic HJContinuedFraction(w:: FldQuadElt) -> Any
{Compute the head and periodic parts of the Hirzebruch--Jung continued fraction expansion of w}
    stop := false;
    steps := [];
    coefficients := [];
    head := [];
    periodic := [];
    while not stop do
	a := UpperIntegerPart(w);
	Append(~steps, w);
	Append(~coefficients, a);
	if (w eq a) then
	    // w is a rational number; stop
	    head := coefficients;
	    return head, periodic;
	end if;
	nextw := -1/(w - a);
	// Check if nextw already appears in previously computed algebraic numbers
	n := Index(steps, nextw);
	if (n gt 0) then //Periodic continued fraction has been found
	    stop := true;
	    head := coefficients[1..n-1];
	    periodic := coefficients[n..#coefficients];
	end if;
	w := nextw;
    end while;
    return head, periodic;
end intrinsic;
 
