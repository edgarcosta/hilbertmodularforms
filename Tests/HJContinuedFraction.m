printf "Testing Hirzebruch-Jung continued fractions of real quadratic elements... ";

//Example from Avi's talk
F<a> := QuadraticField(13);
w := (5+a)/6;
L1, L2 := HJContinuedFraction(w);

assert L1 eq [];
assert L2 eq [2,2,5];

F<a> := QuadraticField(79);
w := 9 + a;
L1, L2 := HJContinuedFraction(w);

assert L1 eq [];
assert L2 eq [18,9];


return true;

