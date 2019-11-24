


intrinsic TraceForm(Mk::ModFrmHilD) -> ModFrmHilDElt
  {Creates the trace form in the space Mk}
  M := Parent(Mk);
  ZF := Integers(M);
  Q := Rationals();
  bbs := NarrowClassGroupReps(M);
  coeffs := AssociativeArray(bbs);
  for bb in bbs do
    coeffs[bb] := AssociativeArray();
    for a in ShintaniReps(M)[bb] do
      coeffs[bb][a*ZF] := Q!TracePrecomputation(Mk,a);
    end for;
  end for;
  elt := HMF(Mk, coeffs);
  return elt;
end intrinsic;


/*


intrinsic CoprimeTraceForm(Mk::ModFrmHilD) -> ModFrmHilDElt
  {Creates the trace form in the space Mk}
  M := Parent(Mk);
  ZF := Integers(M);
  NN := Level(Mk);
  Q := Rationals();
  bbs := NarrowClassGroupReps(M);
  coeffs := AssociativeArray(bbs);
  for bb in bbs do
    coeffs[bb] := AssociativeArray();
    for a in ShintaniReps(M)[bb] do
      if Norm(Gcd(a*ZF,NN)) eq 1 then 
        coeffs[bb][a*ZF] := Q!TracePrecomputation(Mk,a);
      else 
        coeffs[bb][a*ZF] := Q!0;
      end if;
    end for;
  end for;
  elt := HMF(Mk, coeffs);
  return elt;
end intrinsic;

*/