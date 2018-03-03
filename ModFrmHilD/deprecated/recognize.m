// user defined verbose flags
  declare verbose Recognize, 1;

intrinsic MakeK(uCC::Any, m::Any) -> Any, Any, Any, Any, Any
  {MakeK!  What more to say?}
  if m eq 1 then
    vprint Recognize : "Degree bound is 1, so taking RationalsAsNumberField.";
    K := RationalsAsNumberField();
    v := RealPlaces(K)[1];
    return true, K, v, false, Parent(uCC)!1;
  end if;
  vprintf Recognize : "Trying to MakeK with m = %o\n", m;
  CC := Parent(uCC);
  eps := 10^(-Precision(CC)/2);
  u_pol := PowerRelation(uCC, m : Al := "LLL");
  if Degree(u_pol) ne m or not IsIrreducible(u_pol) then
    if Degree(u_pol) gt 1 then
      vprintf Recognize : "Degree bound %o failed, looked like degree %o\n", m, [<Degree(c[1]),c[2]> : c in Factorization(u_pol)];
    end if;
    return false, _, _, _, _;
  end if;
  lc := LeadingCoefficient(u_pol);
  K0 := NumberField(u_pol);
  u0 := K0.1;
  K := NumberField(MinimalPolynomial(lc*u0));
  u := K.1/lc;
  ps, foobar := TrialDivision(Discriminant(K));
  if #foobar gt 0 and not &and[IsSquare(foobarf) : foobarf in foobar] then
    return false, _, _, _, _;
  end if;
  if foobar eq [] then
    vprintf Recognize : "coefficient found, with ps = %o and foobar = []\n", ps;
  else
    vprintf Recognize : "coefficient found, with ps = %o and sqrt(foobar) = %o\n", ps, Round(Sqrt(CC!foobar[1]));
  end if;
  vprintf Recognize : "%o\n", K;
  vprint Recognize : "  ...Trying to optimize";
  Kop, iotaop := OptimizedRepresentation(K : Ramification := [p[1] : p in ps]);
  uop := iotaop(u);
  vprintf Recognize : "  ...successfully optimized\n  Kop = %o\n  now finding complex embedding\n", Kop;
  minv, vind := Min([Abs(uCC-Evaluate(uop,v : Precision := Precision(CC))) : v in InfinitePlaces(Kop)]);
  if minv gt eps then
    // Need complex conjugate
    minv, vind := Min([Abs(Conjugate(uCC)-Evaluate(uop,v : Precision := Precision(CC))) : v in InfinitePlaces(Kop)]);
    conj := true;
  else
    conj := false;
  end if;
  if minv gt eps then
    vprint Recognize : "  ...failed to match; got a polynomial but it apparently sux";
    return false, _, _, _, _;
  end if;
  vprint Recognize : "  ...quality of match", RealField(4)!minv;
  v := InfinitePlaces(Kop)[vind];
  // return true, Kop, v, conj, uop;
  return true, Kop, v, conj, uCC;
end intrinsic;

intrinsic RecognizeOverK(z::FldComElt, K::FldAlg, v::PlcNumElt, conj::BoolElt) -> Any
  {Recognizes a complex number as an element of K with respect to the embedding v, conjugated if conj.}
  CC := Parent(z);
  prec := Precision(CC);
  ZK := Integers(K);
  ZKbCC := [CC!Evaluate(b,v : Precision := Precision(CC)) : b in Basis(ZK)];
  if conj then
    ZKbCC := [Conjugate(zkb) : zkb in ZKbCC];
  end if;
  m := Degree(K);
  if m eq 1 then
    if AbsoluteValue(Im(z)) ge 10^(-prec/2) then
      error "nonzero imaginary part cannot be recognized over rationals.\n";
    end if;
    lin := LinearRelation(ZKbCC cat [-Re(z)] : Al := "LLL");
  else
    lin := LinearRelation(ZKbCC cat [-z] : Al := "LLL");
  end if;
  z_K := (ZK!lin[1..m])/lin[m+1];
  z_K := K!z_K;
  return z_K;
end intrinsic;

intrinsic RecognizeOverQQ(z::FldComElt) -> Any
  {recognize rational number living in RationalsAsNumberField.}
  bl, QQ, v, conj, zCC := MakeK(z, 1);
  if bl then
    return RecognizeOverK(z, QQ, v, conj);
  else
    error "unable to make field!";
  end if;
end intrinsic;

intrinsic RecognizeOverQQ(z::FldReElt) -> Any
  {overloaded to take real number.}
  prec := Precision(Parent(z));
  z := ComplexField(prec)!z;
  bl, QQ, v, conj, zCC := MakeK(z, 1);
  if bl then
    return RecognizeOverK(z, QQ, v, conj);
  else
    error "unable to make field!";
  end if;
end intrinsic;

intrinsic RecognizeQQ(z::FldComElt) -> FldRatElt
  {recognize rational number living in Rationals.}
  return Rationals()!RecognizeOverQQ(z);
end intrinsic;

intrinsic RecognizeQQ(z::FldReElt) -> FldRatElt
  {overloaded to take real number.}
  return Rationals()!RecognizeOverQQ(z);
end intrinsic;

intrinsic RecognizeNumber(z::FldComElt, m::RngIntElt : rationals_as_number_field := false, return_errors := false) -> Any
  {Try to recognize complex number over a number field of degree m and decreasing m as necessary. Setting rationals_as_number_field  true will try to return FldNumElt instead of FldRatElt in the case that z is a rational number. If return_errors is true then a sequence of error messages is returned, SetVerbose("Recognize", 1) for verbose printing.}
  errors := [];
  for i := m to 1 by -1 do
    try
      if i eq 1 then
        if rationals_as_number_field then
          vprintf Recognize : "trying to recognize number in RationalsAsNumberField:\n", i;
          return RecognizeOverQQ(z);
        else // Rationals
          vprintf Recognize : "trying to recognize number in QQ:\n", i;
          return RecognizeQQ(z);
        end if;
      else
        vprintf Recognize : "trying to recognize number in a degree %o number field:\n", i;
        bl, K, v, conj, zCC := MakeK(z, i);
        if bl then
          return RecognizeOverK(z, K, v, conj);
        else
          error "unable to make field!";
        end if;
      end if;
    catch e1
      Append(~errors, e1);
    end try;
  end for;
  if return_errors then
    return errors;
  else
    error "recogniztion failed, set return_errors := true to see a list of error messages.";
  end if;
end intrinsic;

intrinsic RecognizeNumber(z::FldReElt, m::RngIntElt : rationals_as_number_field := false, return_errors := false) -> Any
  {overloaded to take real number.}
  prec := Precision(Parent(z));
  z := ComplexField(prec)!z;
  return RecognizeNumber(z, m : rationals_as_number_field := rationals_as_number_field, return_errors := return_errors);
end intrinsic;
