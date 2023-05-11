/*
  Usage: Make an input file input.txt each of whose rows consists of an LMFDB field label and an LMFDB ideal label separated by a space using GenerateFieldsAndLevels. E.g., 

  2.2.12.1 1.1
  2.2.12.1 2.1
  2.2.12.1 3.1  

  Then run the following command in ~/github/hilbertmodularforms

  parallel -j 16 --joblog joblog --eta -a input.txt echo magma -b F_lab:={1} NN_lab:={2} ModFrmHilD/CanonicalRing/CanonicalRingsScript.m >> ../hilbertmodularsurfacesdata/CanonicalRingEquations.m
*/

AttachSpec("spec");

try 
  WriteCanonicalRingComputationToFile(F_lab,NN_lab);
  exit 0;
catch e
  WriteStderr(e);
  exit 1;
end try;
