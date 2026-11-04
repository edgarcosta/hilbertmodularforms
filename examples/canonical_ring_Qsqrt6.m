// The Theorem 5 comparison assumes the sign action on the published generators.
procedure test_theorem_5_comparison(literature_data)
  label := "2.2.24.1-1.1";
  components := LoadStoredCanonicalRings(label);
  sane, report := VerifyCanonicalRingComponents(label, components);
  assert sane;

  matches := [i : i in [1..#components] | components[i][1] eq "1.1"];
  assert #matches eq 1;
  J := components[matches[1]][2];
  T := Generic(J);
  I, PhiImages, PsiImages, citation, componentLabel := literature_data(T, T);
  assert componentLabel eq components[matches[1]][1];
  assert VerifyGradedIsomorphism(I, J, PhiImages, PsiImages);
end procedure;

// The runner requires eval-loaded literature data at top level.
litfile := "Verification/LiteratureEquations/2.2.24.1-1.1-vdGeer.m";
LitData := eval(Read(litfile) cat "\nreturn LitData;");
test_theorem_5_comparison(LitData);
