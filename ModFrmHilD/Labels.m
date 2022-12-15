
intrinsic LMFDBLabel(F::FldNum) -> MonStgElt
 { LMFDB label for quadratic fields }
 n := Degree(F);
 require n eq 2: "only quadratic fields for now";
 D := Discriminant(Integers(F));
 real_places := D gt 0 select 2 else 0;
 return Sprintf("%o.%o.%o.1", n, real_places, Abs(D));
end intrinsic;
