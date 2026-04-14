// Test: WriteCanonicalRingComputationToString produces valid output
// Verifies the IO layer correctly wraps HilbertModularVariety for Q(sqrt(13))
// Resources: ~20s CPU, <200 MB RAM
printf "WriteCanonicalRingComputationToString on Q(sqrt(13))...";
t0 := Cputime(); walltime := Time();

// Use LMFDBField to get the field with polredabs polynomial (required by LMFDBLabel)
F := LMFDBField("2.2.13.1");
ZF := Integers(F);
NN := 1*ZF;

// Call WriteCanonicalRingComputationToString
s, label := WriteCanonicalRingComputationToString(F, NN);
assert #s gt 0;
assert #label gt 0;

// The output should contain Magma code defining a scheme
// and certification/sanity check comments
assert "R<[x]>" in s;
assert "Scheme" in s;
assert "eqns" in s;
assert "Certified" in s or "Warning" in s;
assert "Sanity check" in s;

printf "PASSED (CPU: %os, Wall: %os, Mem: %oMB)\n", Cputime(t0), Time(walltime), GetMemoryUsage() div (1024^2);
