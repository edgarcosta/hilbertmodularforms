F<r> := QuadraticField(5);
vs := InfinitePlaces(F);
evs := [Evaluate(r, v) : v in vs];
HJContinuedFraction(evs[1]);
VerifyExactHJContinuedFraction(r);
