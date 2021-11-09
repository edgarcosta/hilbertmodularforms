
//////////////////// Main function: Trace Form /////////////////////////

intrinsic TraceForm(Mk::ModFrmHilD) -> ModFrmHilDElt
  {Creates the trace form in the space Mk}
  M := Parent(Mk);
  Q := Rationals();
  coeffs := AssociativeArray();
  for bb in NarrowClassGroupReps(M) do
    coeffs[bb] := AssociativeArray();
    for nu->nn in ShintaniRepsIdeal(M)[bb] do
      coeffs[bb][nu] := Q!Trace(Mk, nn);
    end for;
  end for;
  return HMF(Mk, coeffs);
end intrinsic;

//////////////////// Main function: Speed Trace Form /////////////////////////

intrinsic STraceForm(Mk::ModFrmHilD) -> ModFrmHilDElt
  {Creates the trace form in the space Mk}
  M := Parent(Mk);
  Q := Rationals();
  coeffs := AssociativeArray();
  for bb in NarrowClassGroupReps(M) do
    coeffs[bb] := AssociativeArray();
    for nu->nn in ShintaniRepsIdeal(M)[bb] do
      coeffs[bb][nu] := Q!STrace(Mk, nn);
    end for;
  end for;
  return HMF(Mk, coeffs);
end intrinsic;
