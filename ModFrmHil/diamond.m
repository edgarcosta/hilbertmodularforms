// originally from hecke.m

function hecke_matrix_field(M : hack := true)
  if assigned M`hecke_matrix_field then
    return M`hecke_matrix_field;
  elif IsBianchi(M) or not IsDefinite(M) then
    return Rationals();
  else
      if hack then
	  // hack begins
	  return TopAmbient(M)`weight_base_field;
	  // hack ends
      else
	  return Ambient(M)`weight_base_field;
      end if;
  end if;
end function;
