
//////////////////// Main function: Trace Form /////////////////////////

intrinsic TraceForm(Mk::ModFrmHilD) -> ModFrmHilDElt
  {Creates the trace form in the space Mk}
  M := Parent(Mk);
  Q := Rationals();
  bbs := NarrowClassGroupReps(M);
  coeffs := AssociativeArray(bbs);
  for bb in bbs do
    coeffs[bb] := AssociativeArray();
    for I in IdealsByNarrowClassGroup(M)[bb] do
      coeffs[bb][I] := Q!Trace(Mk,I);
    end for;
  end for;
  elt := HMF(Mk, coeffs: CoeffsByIdeal:=true);
  return elt;
end intrinsic;

//////////////////// Main function: Speed Trace Form /////////////////////////

intrinsic STraceForm(Mk::ModFrmHilD) -> ModFrmHilDElt
  {Creates the trace form in the space Mk}
  M := Parent(Mk);
  Q := Rationals();
  bbs := NarrowClassGroupReps(M);
  coeffs := AssociativeArray(bbs);
  for bb in bbs do
    coeffs[bb] := AssociativeArray();
    for I in IdealsByNarrowClassGroup(M)[bb] do
      coeffs[bb][I] := Q!STrace(Mk,I);
    end for;
  end for;
  elt := HMF(Mk, coeffs: CoeffsByIdeal:=true);
  return elt;
end intrinsic;





//////////////////// Main function: Trace Form (Old) /////////////////////////

/*
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



intrinsic CoprimeLinearDependence(List::SeqEnum[ModFrmHilDElt],mm::RngOrdIdl) -> SeqEnum[RngIntElt]
  {finds a small non-trivial integral linear combination between components of v away from nn. If none can be found return 0.}
  M := GradedRing(List[1]);
  bbs := NarrowClassGroupReps(M);
  CoeffLists := [[] : i in [1..#List]];
  for bb in bbs do
    for nn in IdealsByNarrowClassGroup(M)[bb] do
      if Norm(Gcd(mm,nn)) eq 1 then
        for i in [1..#List] do
          Append(~CoeffLists[i], Coefficients(List[i])[bb][nn]);
        end for;
      end if;
    end for;
  end for;
  return LinearDependence(CoeffLists);
end intrinsic;
*/
