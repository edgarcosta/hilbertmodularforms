forward IsBianchi;
forward Ambient;
import "finitefield.m" : reduction_mod_random_large_split_prime;
import !"Geometry/ModFrmHil/hecke.m" :
  hecke_algebra_dimension,
  random_large_split_prime,
  reduction;


/********************   from hackobj.m    *********************/
function IsBianchi(M)
  return ISA(Type(M), ModFrmBianchi);
end function;

function Ambient(M)
  if assigned M`Ambient then
    return M`Ambient;
  else
    // must have decided how to compute M
    assert assigned M`QuaternionOrder or IsBianchi(M);
    return M;
  end if;
end function;

function TopAmbient(M)
  top := M;
  while assigned top`Ambient do
    top := top`Ambient;
  end while;
  return top;
end function;

// create Bianchi space with given ambient
function BMF_with_ambient(A)
  assert not assigned A`Ambient;
  M := New(ModFrmBianchi);
  M`Ambient := A;
  M`Field := A`Field;
  M`Level := A`Level;
  M`DirichletCharacter := 1;
  M`Weight := [2];
  M`CentralCharacter := 0;
  M`is_cuspidal := true; // always true, currently
  M`homology_coefficients := A`homology_coefficients;
  M`ModFrmData := A`ModFrmData;
  M`LevelData := A`LevelData;
  M`Hecke := AssociativeArray();
  M`HeckeCharPoly := AssociativeArray();
  return M;
end function;

function HMF0(F, N, Nnew, Chi, k, C)
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
  if forall{w : w in k | w eq 2} then
    M`hecke_matrix_field := Rationals();
    M`hecke_matrix_field_is_minimal := true;
  else
    M`hecke_matrix_field_is_minimal := false;
  end if;
  return M;
end function;

/********************   from definite.m    *********************/
// Tensor product is associative; for efficiency always do
// TensorProduct(small_mat, large_mat)

function weight_map_arch(q, splittings, K, m, n)
   d := #m;
   M := MatrixRing(K,1)!1;
   for l := d to 1 by -1 do
      if m[l] eq 0 and n[l] eq 0 then
         // don't need to modify M
         continue;
      else
         matq := splittings[l](q);
         if n[l] eq 0 then
            M *:= Determinant(matq)^m[l];
         else
            if n[l] eq 1 then
               Ml := matq;
            else
               Ml := SymmetricPower2(matq, n[l]);
            end if;
            if m[l] ne 0 then
               Ml *:= Determinant(matq)^m[l];
            end if;
            if l eq d then
               M := Ml;
            else
               M := TensorProduct(Ml, M);
            end if;
         end if;
      end if;
   end for;
   return M;
end function;
