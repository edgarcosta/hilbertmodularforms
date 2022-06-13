// copied from ModFrmHil/hackobj.m and modified
freeze;

import "copypaste/hackobj.m" : HMF;
/*
function HMF0(F, N, Nnew, Chi, k, C : hack := true)
  M := New(ModFrmHil);
  M`Field := F;
  M`Level := N;
  M`NewLevel := Nnew;
  M`DirichletCharacter := Chi;
  M`Weight := k;
  M`CentralCharacter := C;
  assert C eq Max(k) - 2; // currently
  M`is_cuspidal := true; // always true, currently
  M`Hecke    := AssociativeArray();
  M`HeckeBig := AssociativeArray();
  M`HeckeBigColumns := AssociativeArray();
  M`HeckeCharPoly := AssociativeArray();
  M`AL       := AssociativeArray();
  M`DegDown1 := AssociativeArray();
  M`DegDownp := AssociativeArray();
  // hack begins
//  if hack then
//      M`Diamond := AssociativeArray();
//  end if;
  // hack ends
  if forall{w : w in k | w eq 2} then
    M`hecke_matrix_field := Rationals();
    M`hecke_matrix_field_is_minimal := true;
  else 
    M`hecke_matrix_field_is_minimal := false;
  end if;
  return M;
end function;
*/

intrinsic HilbertCuspForms(F::FldNum, N::RngOrdIdl, chi::GrpHeckeElt,
			   k::SeqEnum[RngIntElt] : 
			   QuaternionOrder:=0) -> ModFrmHil 
{The space of Hilbert modular forms over the totally real number field F, 
    with level N , character chi and weight k (or parallel weight 2, if k is not specified).  
 Here N should be an ideal in the maximal order of F, chi should be a Hecke character and k should be a 
 sequence of integers.
 If the optional argument QuaternionOrder is specified, this order 
 will be used for all computations of the space.}

  require NumberField(Order(N)) eq F :
         "The level N must be an ideal in the base field";
  require IsAbsoluteField(F) : 
         "The base field F must be an absolute extension of Q";
  require IsTotallyReal(F) : 
         "The base field F must be totally real";
  require #k eq Degree(F) : 
         "The weight k should be a sequence of d integers, where d is the degree of the field";
  // TODO : Do we still want to leave this?
  require IsArithmeticWeight(F, k) :
         "The weight should be a sequence of integers that are all at least 2, and all of the same parity";
  require IsCompatibleWeight(chi, k) :
         "The weight should be compatible with the character.";
  
  return HMF(F, N, k : Chi := chi, QuaternionOrder:=QuaternionOrder);
end intrinsic;

intrinsic HilbertCuspForms(F::FldNum, N::RngOrdIdl, chi::GrpHeckeElt,
			   k::RngIntElt : QuaternionOrder:=0) -> ModFrmHil 
{"} // "
  require NumberField(Order(N)) eq F :
         "The level N must be an ideal in the base field";
  require IsAbsoluteField(F) : 
         "The base field F must be an absolute extension of Q";
  require IsTotallyReal(F) : 
         "The base field F must be totally real";
  require IsCompatibleWeight(chi, k) :
         "The weight should be compatible with the character.";
     
  k := [k : i in [1..Degree(F)]];
  return HMF(F, N, k : Chi := chi, QuaternionOrder:=QuaternionOrder);
end intrinsic;

intrinsic HilbertCuspForms(F::FldNum, N::RngOrdIdl, chi::GrpHeckeElt
			   : QuaternionOrder:=0) 
       -> ModFrmHil 
{"} // "
  require NumberField(Order(N)) eq F :
         "The level N must be an ideal in the base field";
  require IsAbsoluteField(F) : 
         "The base field F must be an absolute extension of Q";
  require IsTotallyReal(F) : 
         "The base field F must be totally real";
  require IsCompatibleWeight(chi, 2) :
         "The weight should be compatible with the character.";
	 
  k := [2 : i in [1..Degree(F)]];
  return HMF(F, N, k : Chi := chi, QuaternionOrder:=QuaternionOrder );
end intrinsic;

intrinsic HilbertCuspForms(F::FldRat, N::RngInt, chi::GrpHeckeElt,
			   k::RngIntElt : QuaternionOrder:=0)
       -> ModFrmHil
{The space of modular forms over the rationals with level N, character chi and weight k
 (or weight 2, if k is not specified).
 If the optional argument QuaternionOrder is specified, this quaternion order 
 will be used for all computations of the space.}
 
  require k eq 2 : 
    "Over Rationals(), only implemented for weight 2.  Use RationalsAsNumberField() instead.";
  return HMF(F, N, [k] : Chi := chi, QuaternionOrder:=QuaternionOrder );
end intrinsic;

intrinsic HilbertCuspForms(F::FldRat, N::RngIntElt, chi::GrpHeckeElt,
		           k::RngIntElt : QuaternionOrder:=0) -> ModFrmHil
{"} // "
  require k eq 2 : 
    "Over Rationals(), only implemented for weight 2.  Use RationalsAsNumberField() instead.";
  return HMF(F, N*Integers(), [k] : Chi := chi, QuaternionOrder:=QuaternionOrder );
end intrinsic;

intrinsic HilbertCuspForms(F::FldRat, N::RngInt, chi::GrpHeckeElt,
		           k::SeqEnum[RngIntElt] : QuaternionOrder:=0) -> ModFrmHil
{"} // "
  require k eq [2] : 
    "Over Rationals(), only implemented for weight 2.  Use RationalsAsNumberField() instead.";
  return HMF(F, N, k : Chi := chi, QuaternionOrder:=QuaternionOrder );
end intrinsic;

intrinsic HilbertCuspForms(F::FldRat, N::RngIntElt, chi::GrpHeckeElt,
			   k::SeqEnum[RngIntElt] : QuaternionOrder:=0) -> ModFrmHil
{"} // "
  require k eq [2] : 
    "Over Rationals(), only implemented for weight 2.  Use RationalsAsNumberField() instead.";
  return HMF(F, N*Integers(), k : Chi := chi, QuaternionOrder:=QuaternionOrder );
end intrinsic;

intrinsic HilbertCuspForms(F::FldRat, N::RngInt, chi::GrpHeckeElt : QuaternionOrder:=0) -> ModFrmHil
{"} // "
  return HMF(F, N, [2] : Chi := chi, QuaternionOrder:=QuaternionOrder );
end intrinsic;

intrinsic HilbertCuspForms(F::FldRat, N::RngIntElt, chi::GrpHeckeElt : QuaternionOrder:=0) -> ModFrmHil
{"} // "
  return HMF(F, N*Integers(), [2] : Chi := chi, QuaternionOrder:=QuaternionOrder );
end intrinsic;
