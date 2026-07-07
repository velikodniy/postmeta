input plain;
beginfig(134)
  u:=1cm;
  numeric n,m; n:=3; m:=3;
  pair A[], B[];
  for i=1 upto n-1: A[i+1]-A[i] = (.5u,0); endfor;
  for j=1 upto m-1: B[j+1]-B[j] = (.5u,0); endfor;
  (0,0) for i=1 upto n: + A[i] endfor  = (0,0);
  (0,0) for j=1 upto m: + B[j] endfor  = (0,4u);
  for i=1 upto n:
    draw A[i] withpen pencircle scaled 4bp;
  endfor;
  for j=1 upto m:
    draw B[j] withpen pencircle scaled 4bp;
  endfor;
  for i=1 upto n:
    for j=1 upto m:
      draw A[i]--B[j];
    endfor;
  endfor;
endfig;
end;
