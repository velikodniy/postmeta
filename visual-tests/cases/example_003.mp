input plain;
beginfig(3)
  pair A[];
  A[0]:=(-1cm, -1cm);
  A[1]:=( 1cm, -1cm);
  A[2]:=( 1cm,  1cm);
  A[3]:=(-1cm,  1cm);
  draw A[0]--A[1]--A[2]--A[3]--cycle;
  draw A[0]--A[2];
  draw A[1]--A[3];
endfig;
end;
