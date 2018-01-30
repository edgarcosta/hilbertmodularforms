174,0
T,ModFrmHilD,ModFrmHilDElt,0
A,ModFrmHilD,4,Field,Level,Weight,CoefficientRing
S,Print,,0,1,0,0,1,0,0,0,0,ModFrmHilD,,-38,-38,-38,-38,-38,-38
S,in,,0,2,0,0,0,0,0,0,0,ModFrmHilD,,0,0,-1,,36,-38,-38,-38,-38,-38
S,eq,True iff every attribute of M1 is equal to the corresponding attribute of M2,0,2,0,0,0,0,0,0,0,ModFrmHilD,,0,0,ModFrmHilD,,36,-38,-38,-38,-38,-38
S,IsCoercible,,0,2,0,0,0,0,0,0,0,-1,,0,0,ModFrmHilD,,36,-1,-38,-38,-38,-38
S,ModFrmHilDInitialize,Create an empty ModFrmHilD object,0,0,0,0,0,0,0,ModFrmHilD,-38,-38,-38,-38,-38
S,HMFSpace,"Generates the space ModFrmHilD over F with level N, weights k, and coefficient ring ZK",1,2,1,82,0,148,4,0,0,0,0,0,0,0,27,,0,0,82,,0,0,217,,0,0,27,,ModFrmHilD,-38,-38,-38,-38,-38
S,HMFSpace,"Generates the space ModFrmHilD over F with level N, weights k, and coefficient ring ZZ",1,2,1,82,0,148,4,0,0,0,0,0,0,0,262,,0,0,82,,0,0,217,,0,0,27,,ModFrmHilD,-38,-38,-38,-38,-38
S,HMFSpace,"Generates the space ModFrmHilD over F with level N, weights k, and coefficient ring ZZ",1,2,1,82,0,148,3,0,0,0,0,0,0,0,82,,0,0,217,,0,0,27,,ModFrmHilD,-38,-38,-38,-38,-38
S,ModFrmHilDCopy,new instance of ModFrmHilD,0,1,0,0,0,0,0,0,0,ModFrmHilD,,ModFrmHilD,-38,-38,-38,-38,-38
S,BaseField,The base field of the space M of Hilbert modular forms,0,1,0,0,0,0,0,0,0,ModFrmHilD,,-9,-38,-38,-38,-38,-38
S,Level,The level of the space M of Hilbert modular forms,0,1,0,0,0,0,0,0,0,ModFrmHilD,,RngOrgIdl,-38,-38,-38,-38,-38
S,Weight,The weight of the space M of Hilbert modular forms,0,1,0,0,0,0,0,0,0,ModFrmHilD,,82,-38,-38,-38,-38,-38
S,CoefficientRing,The coefficient ring of the space M of Hilbert modular forms,0,1,0,0,0,0,0,0,0,ModFrmHilD,,-9,-38,-38,-38,-38,-38
T,ModFrmHilDElt,-,0
A,ModFrmHilDElt,3,Parent,Precision,Coefficients
S,Print,,0,1,0,0,1,0,0,0,0,ModFrmHilDElt,,-38,-38,-38,-38,-38,-38
S,in,,0,2,0,0,0,0,0,0,0,ModFrmHilDElt,,0,0,-1,,36,-38,-38,-38,-38,-38
S,IsCoercible,,0,2,0,0,0,0,0,0,0,-1,,0,0,ModFrmHilDElt,,36,-1,-38,-38,-38,-38
S,eq,check compatibility and coefficient equality up to minimum precision,0,2,0,0,0,0,0,0,0,ModFrmHilDElt,,0,0,ModFrmHilDElt,,36,-38,-38,-38,-38,-38
S,Preceq,check compatibility and coefficient equality and see if both have the same precision,0,2,0,0,0,0,0,0,0,ModFrmHilDElt,,0,0,ModFrmHilDElt,,36,-38,-38,-38,-38,-38
S,Parent,returns ModFrmHilD space where f lives,0,1,0,0,0,0,0,0,0,ModFrmHilDElt,,ModFrmHilD,-38,-38,-38,-38,-38
S,Precision,returns precision of expansion for f which bounds the norm of ideals in the expansion,0,1,0,0,0,0,0,0,0,ModFrmHilDElt,,148,-38,-38,-38,-38,-38
S,Coefficients,returns associative array of coefficients indexed by IdealsUpTo Precision(f),0,1,0,0,0,0,0,0,0,ModFrmHilDElt,,457,-38,-38,-38,-38,-38
S,BaseField,returns base field of parent of f,0,1,0,0,0,0,0,0,0,ModFrmHilDElt,,27,-38,-38,-38,-38,-38
S,Level,returns level of parent of f,0,1,0,0,0,0,0,0,0,ModFrmHilDElt,,217,-38,-38,-38,-38,-38
S,Weight,returns weight of parent of f,0,1,0,0,0,0,0,0,0,ModFrmHilDElt,,82,-38,-38,-38,-38,-38
S,CoefficientRing,returns coefficient ring of expansion f which is ZK or ZZ,0,1,0,0,0,0,0,0,0,ModFrmHilDElt,,-44,-38,-38,-38,-38,-38
S,ModFrmHilDEltInitialize,Create an empty ModFrmHilDElt object,0,0,0,0,0,0,0,ModFrmHilDElt,-38,-38,-38,-38,-38
S,ModFrmHilDEltCopy,new instance of ModFrmHilDElt,0,1,0,0,0,0,0,0,0,ModFrmHilDElt,,ModFrmHilDElt,-38,-38,-38,-38,-38
S,HMFZero,"creates the zero ModFrmHilDElt over F with level N, weights k, coefficient ring ZK, and precision prec",1,2,1,82,0,148,5,0,0,0,0,0,0,0,148,,0,0,27,,0,0,82,,0,0,217,,0,0,27,,ModFrmHilDElt,-38,-38,-38,-38,-38
S,HMFZero,"creates the zero ModFrmHilDElt over F with level N, weights k, coefficient ring ZZ, and precision prec",1,2,1,82,0,148,5,0,0,0,0,0,0,0,148,,0,0,262,,0,0,82,,0,0,217,,0,0,27,,ModFrmHilDElt,-38,-38,-38,-38,-38
S,HMF,creates the corresponding ModFrmHilDElt with some sanity checking,1,2,1,82,0,148,6,0,0,0,0,0,0,0,148,,0,0,457,,0,0,27,,0,0,82,,0,0,217,,0,0,27,,ModFrmHilDElt,-38,-38,-38,-38,-38
S,EigenformToHMF,Construct the ModFrmHilDElt in M determined (on prime ideals up to norm prec) by hecke_eigenvalues,0,3,0,0,0,0,0,0,0,148,,0,0,457,,0,0,ModFrmHilD,,ModFrmHilDElt,-38,-38,-38,-38,-38
S,*,scale f by integer c,0,2,0,0,0,0,0,0,0,ModFrmHilDElt,,0,0,148,,ModFrmHilDElt,-38,-38,-38,-38,-38
S,*,scale f by integral element c,0,2,0,0,0,0,0,0,0,ModFrmHilDElt,,0,0,216,,ModFrmHilDElt,-38,-38,-38,-38,-38
S,+,return f+g,0,2,0,0,0,0,0,0,0,ModFrmHilDElt,,0,0,ModFrmHilDElt,,ModFrmHilDElt,-38,-38,-38,-38,-38
S,*,return f*g,0,2,0,0,0,0,0,0,0,ModFrmHilD,,0,0,ModFrmHilD,,ModFrmHilD,-38,-38,-38,-38,-38
S,IsAdmissibleWeight,Decide if the sequence of weights k can be used for the weight of a ModFrmHilD,1,1,1,82,0,148,2,0,0,0,0,0,0,0,82,,0,0,27,,36,-38,-38,-38,-38,-38
