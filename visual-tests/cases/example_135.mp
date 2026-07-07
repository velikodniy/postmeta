input plain;
beginfig(135)
  pair A[], B[];
  numeric n; n:=6;
  for i=0 upto n-1:
    A[i] = 1cm * right rotated (i*360/n);
    B[i] = 2cm * right rotated (i*360/n);
  endfor;
  A[n] = A[0]; B[n] = B[0];
  for i=0 upto n-1:
    draw A[i] -- A[i+1] -- B[i+1] -- B[i];
    draw A[i] withpen pencircle scaled 4bp;
    draw B[i] withpen pencircle scaled 4bp;
  endfor;
endfig;
end;
