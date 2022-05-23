// copied from ModFrmHil/hackobj.m and modified
freeze;

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
