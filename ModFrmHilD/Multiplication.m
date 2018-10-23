/////////// Multiplication ////////////

/*

TODO 

1) Clean up IndicesbyTrace. Currently messy but fast.
2) ShintaniDomain. Idea is simple but I did a bad job.

*/


intrinsic EmbedNumberField(nu::RngOrdElt, places::[PlcNumElt]) -> SeqEnum
  {Input: nu an element of ZF where F is totally real
   Output: A tuple of the real embeddings of nu in RR}
  
  return [Evaluate(nu, pl) : pl in places];
end intrinsic;



intrinsic NiceBasis(ZF::RngOrd) -> SeqEnum
  {Input: ZF ring of integers of a number field
   Output: A basis for ZF that puts the trace in Smith normal form}
  
  Z := Integers();
  Tr := Matrix([[Z!Trace(ZF.i) : i in [1..Degree(ZF)]]]);
  Sm,P,Q := SmithForm(Tr);
  B1 := [ZF!ElementToSequence(Transpose(Q)[i]) : i in [1..Degree(ZF)]];
  return B1;
end intrinsic;



intrinsic IndicesByTraceQuadratic(N::RngIntElt, ZF::RngOrd, places::[PlcNumElt]) -> SeqEnum
  { Input: N integer for the trace, ZF ring of integers, places set of places of F
    Output: All elements of ZFgeq0 with trace N}

  	d := Discriminant(ZF);
  	if d mod 4 eq 0 then
    	d := d div 4;
  	end if;

	I := [];
    if d mod 4 eq 1 then
    	L := Ceiling((1 - 1 / Sqrt(d)) * N / 2);
    	U := Floor((1 + 1 / Sqrt(d)) * N / 2);
    	for a in [L..U] do
     		Append(~I, a + (N - 2 * a) * ZF.2);
    	end for;
  	else
    	if N mod 2 eq 1 then
      		return I;
    	else
      		L := Ceiling(-N / (2 * Sqrt(d)));
      		U := Floor(N / (2 * Sqrt(d)));
      		for a in [L..U] do
        		Append(~I, N / 2 + a * ZF.2);
      		end for;
    	end if;
 	 end if;
  	return I;
end intrinsic;



// This code should be reworked
intrinsic IndicesByTraceCubic(N::RngIntElt, ZF::RngOrd, places::[PlcNumElt]) -> List
  {return all totally positive elements of F with trace N}

  O := NiceBasis(ZF);

  if N mod Trace(O[1]) eq 0 then
    
    Z := Integers();
    n := Z!(N/Trace(O[1]));


    fixedvec := EmbedNumberField(n*O[1], places);
    alphai := EmbedNumberField(O[2], places);
    betai := EmbedNumberField(O[3], places);
    

    M := Matrix([alphai,betai]);
    V := -Matrix([fixedvec]);
    M12 := Submatrix(M,[1,2],[1,2]);
    M13 := Submatrix(M,[1,2],[1,3]);
    M23 := Submatrix(M,[1,2],[2,3]);
    V12 := Submatrix(V,[1],[1,2]);
    V13 := Submatrix(V,[1],[1,3]);
    V23 := Submatrix(V,[1],[2,3]);
    
    Vert := [[*Solution(M12,V12),{1,2}*],[*Solution(M13,V13),{1,3}*],[*Solution(M23,V23),{2,3}*]];
    XVert := [Solution(M12,V12)[1][1], Solution(M13,V13)[1][1], Solution(M23,V23)[1][1]];
    ParallelSort(~XVert, ~Vert);
    Xlow := XVert[1]; Xmid := XVert[2];  Xhigh := XVert[3]; 
    Xl := [i : i in Vert[1][2] meet Vert[3][2]][1]; Y1l := [i : i in Vert[1][2] meet Vert[2][2]][1]; Y2l := [i : i in Vert[2][2] meet Vert[3][2]][1];

    All := [];

    if betai[Xl] ge 0 then  
      for i in [Ceiling(Xlow)..Floor(Xmid)] do
        YLow := Ceiling(-(fixedvec[Xl] + alphai[Xl]*i)/betai[Xl]);
        YHigh := Floor(-(fixedvec[Y1l] + alphai[Y1l]*i)/betai[Y1l]);
        for j in [YLow..YHigh] do
          Append(~All,n*O[1]+i*O[2]+j*O[3]);
        end for;
      end for;
      for i in [Ceiling(Xmid)..Floor(Xhigh)] do
        YLow := Ceiling(-(fixedvec[Xl] + alphai[Xl]*i)/betai[Xl]);
        YHigh := Floor(-(fixedvec[Y2l] + alphai[Y2l]*i)/betai[Y2l]);
        for j in [YLow..YHigh] do
          Append(~All,n*O[1]+i*O[2]+j*O[3]);
        end for;
      end for;
    else
      for i in [Ceiling(Xlow)..Floor(Xmid)] do
        YHigh := Floor(-(fixedvec[Xl] + alphai[Xl]*i)/betai[Xl]);
        YLow := Ceiling(-(fixedvec[Y1l] + alphai[Y1l]*i)/betai[Y1l]);
        for j in [YLow..YHigh] do
          Append(~All,n*O[1]+i*O[2]+j*O[3]);
        end for;
      end for;
      for i in [Ceiling(Xmid)..Floor(Xhigh)] do
        YHigh := Floor(-(fixedvec[Xl] + alphai[Xl]*i)/betai[Xl]);
        YLow := Ceiling(-(fixedvec[Y2l] + alphai[Y2l]*i)/betai[Y2l]);
        for j in [YLow..YHigh] do
          Append(~All,n*O[1]+i*O[2]+j*O[3]);
        end for;
      end for;    
    end if; 
    return All;
  else
    return [];
  end if;
end intrinsic; 


//This finds a totally positive element of minimal trace

intrinsic ShintaniDomain(M::ModFrmHilD, ZF::RngOrd, places::[PlcNumElt]) -> any
  {Elicit representatives in the shintani domain in a fast manner}
  A := AssociativeArray();
  B := AssociativeArray();
  ideals := Ideals(M);
  n := Precision(M);

  for i in ideals do
    A[i] := 0;
  end for;

  t := 0;
  i := 0;

  d := Degree(ZF);

  while t lt #ideals do
  	if d eq 2 then 
    	T := IndicesByTraceQuadratic(i, ZF, places);
    elif d eq 3 then 
    	T := IndicesByTraceCubic(i, ZF, places);
    else 
    	print "Not implemented";
    end if;

    for j in T do
      I := ideal<ZF| j>;
      if IsDefined(A,I) then
        if A[I] eq 0 then
          t := t+1;
          A[I] := j;
          B[j] := [];
        end if;
      end if;
    end for;
    i := i+1;
  end while; 

  return A,B,i;  
end intrinsic;





intrinsic GetIndexPairs(M::ModFrmHilD) -> SeqEnum
  {returns list of [nu, [[nu1,nu2],...] ] such that nu1+nu2 = nu up to precision.}
  if NarrowClassNumber(BaseField(M)) ne 1 then
    print "WARNING: currently only works for narrow class number 1.\n";
    assert false;
  end if;

  ZF := Integers(BaseField(M));
  places := InfinitePlaces(BaseField(M));
  ideals := Ideals(M);
  n := Precision(M);
  d := Degree(ZF);

  Shintanielts, result, trace_bound := ShintaniDomain(M,ZF,places); gens := Keys(result);

  by_trace := AssociativeArray();
  for i in [0..trace_bound] do
    
    if d eq 2 then
      s_1 := IndicesByTraceQuadratic(i, ZF, places);
    elif d eq 3 then 
      s_1 := IndicesByTraceCubic(i, ZF, places);
    else
      print "Not Implemented";
    end if;
    
    by_trace[i] := s_1;

    for j in [0..Min(i, trace_bound - i)] do
      for nu_1 in s_1 do
        for nu_2 in by_trace[j] do
          nu := nu_1 + nu_2;
          if IsDefined(result, nu) then
            Append(~result[nu], [nu_1, nu_2]);
            Append(~result[nu], [nu_2, nu_1]);
          end if;
        end for;
      end for;
    end for;
  end for;

  indices_list := [];
  shintani_reps := AssociativeArray();
  for nu in gens do
    sums_up := [];
    for x in Set(result[nu]) do
      if not IsDefined(shintani_reps, x[1]) then
        shintani_reps[x[1]] := Shintanielts[ideal<ZF |x[1]>];
      end if;
      if not IsDefined(shintani_reps, x[2]) then
        shintani_reps[x[2]] := Shintanielts[ideal<ZF |x[2]>];;
      end if;
      Append(~sums_up, [shintani_reps[x[1]], shintani_reps[x[2]]]);
    end for;
    Append(~indices_list, [* nu, sums_up *]);
  end for;
  return indices_list;
end intrinsic;



