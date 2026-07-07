input plain;
beginfig(133)
  u:=2cm;
  numeric n,m; n:=4; m:=5;
  pair A[], B[];
  for i=1 upto n-1: A[i+1]-A[i] = (0,.2u); endfor;
  for j=1 upto m-1: B[j+1]-B[j] = (0,.2u); endfor;
  (0,0) for i=1 upto n: + A[i] endfor  = (0,0);
  (0,0) for j=1 upto m: + B[j] endfor  = (4u,0);
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
