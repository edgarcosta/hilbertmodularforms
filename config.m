// spec
dir := GetCurrentDirectory();
parentdir := Pipe(Sprintf("basename 'dirname %o'", dir), "");
if parentdir eq "hilbertmodularforms\n" then
  repo := dir;
else
  error "make sure your working directory is hilbertmodularforms repository";
end if;
AttachSpec("Code/spec");
// setting
SetColumns(0);
// TODO verbose?
