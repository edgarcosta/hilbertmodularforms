intrinsic MakeK(uCC::Any, m::Any) -> Any, Any, Any, Any, Any
  {MakeK!  What more to say?}
  if m eq 1 then
    vprint Shimura : "  ...m eq 1, so taking QQ";
    K := RationalsAsNumberField();
    v := RealPlaces(K)[1];
    return true, K, v, false, Parent(uCC)!1;
  end if;
  vprintf Shimura : "  ...Trying to MakeK with m = %o\n", m;
  CC := Parent(uCC);
  eps := 10^(-Precision(CC)/2);
  u_pol := PowerRelation(uCC, m : Al := "LLL");
  if Degree(u_pol) ne m or not IsIrreducible(u_pol) then
    if Degree(u_pol) gt 1 then
      vprint Shimura : "  ...coefficient not degree m, looked like degree", [<Degree(c[1]),c[2]> : c in Factorization(u_pol)];
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
    vprintf Shimura : "  ...coefficient found, with ps = %o and foobar = []\n", ps;
  else
    vprintf Shimura : "  ...coefficient found, with ps = %o and sqrt(foobar) = %o\n", ps, Round(Sqrt(CC!foobar[1]));
  end if;
  vprintf Shimura : "  ...%o\n", K;
  vprint Shimura : "  ...Trying to optimize";
  Kop, iotaop := OptimizedRepresentation(K : Ramification := [p[1] : p in ps]);
  uop := iotaop(u);
  vprintf Shimura : "  ...successfully optimized\n  Kop = %o\n  now finding complex embedding\n", Kop;
  minv, vind := Min([Abs(uCC-Evaluate(uop,v : Precision := Precision(CC))) : v in InfinitePlaces(Kop)]);
  if minv gt eps then
    // Need complex conjugate
    minv, vind := Min([Abs(Conjugate(uCC)-Evaluate(uop,v : Precision := Precision(CC))) : v in InfinitePlaces(Kop)]);
    conj := true;
  else
    conj := false;
  end if;
  if minv gt eps then
    vprint Shimura : "  ...failed to match; got a polynomial but it apparently sux";
    return false, _, _, _, _;
  end if;
  vprint Shimura : "  ...quality of match", RealField(4)!minv;
  v := InfinitePlaces(Kop)[vind];
  // return true, Kop, v, conj, uop;
  return true, Kop, v, conj, uCC;
end intrinsic;

intrinsic RecognizeOverK(z::FldComElt, K::FldAlg, v::PlcNumElt, conj::BoolElt) -> Any
  {Recognizes a complex number as an element of K with respect to the embedding v, conjugated if conj.}
  CC := Parent(z);
  ZK := Integers(K);
  ZKbCC := [CC!Evaluate(b,v : Precision := Precision(CC)) : b in Basis(ZK)];
  if conj then
    ZKbCC := [Conjugate(zkb) : zkb in ZKbCC];
  end if;
  m := Degree(K);
  if m eq 1 then
    lin := LinearRelation(ZKbCC cat [-Re(z)] : Al := "LLL");
  else
    lin := LinearRelation(ZKbCC cat [-z] : Al := "LLL");
  end if;
  z_K := (ZK!lin[1..m])/lin[m+1];
  z_K := K!z_K;
  return z_K;
end intrinsic;
