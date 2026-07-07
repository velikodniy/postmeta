input plain;
beginfig(132)
  u:=1cm;
  pair A[];
  numeric n; n:=7;
  A[0] = (u,0);
  for i=1 upto n-1:
    A[i] = A[0] rotated (360/n*i);
  endfor;
  for i=0 upto n-1:
    draw A[i] withpen pencircle scaled 4bp;
    for j=0 upto n-1:
      if i<>j: draw A[i]--A[j] fi;
    endfor;
  endfor;
endfig;
end;
