// Compare stored GL+ component 1.1 with the Theorem 5 invariant candidate.
// The sign action is assumed; its geometric identification is pending.
// Keep eval-loaded data at top level for compatibility with run_tests.m.

label := "2.2.24.1-1.1";
components := LoadStoredCanonicalRings(label);
sane, report := VerifyCanonicalRingComponents(label, components);
assert sane;
assert &and[row[2] : row in report];

matches := [i : i in [1..#components] | components[i][1] eq "1.1"];
assert #matches eq 1;
J := components[matches[1]][2];
T := Generic(J);
litfile := "Verification/LiteratureEquations/2.2.24.1-1.1-vdGeer.m";
LitData := eval(Read(litfile) cat "\nreturn LitData;");
I, PhiImages, PsiImages, citation, storedSHA256, componentLabel := LitData(T, T);
assert componentLabel eq components[matches[1]][1];
storedfile := "Verification/CanonicalRingEquations/2.2.24.1-1.1-gl-0.m";
assert Split(Pipe("sha256sum " cat storedfile, ""), " ")[1] eq storedSHA256;
assert VerifyGradedIsomorphism(I, J, PhiImages, PsiImages);
printf "Q(sqrt6) level 1: all component series verified; component %o algebraically isomorphic to %o under an assumed sign action; geometric identification pending.\n",
    componentLabel, citation;
