input plain;
beginfig(194)
  n:=8;
  u:=5mm;
  for i=0 upto n-1:
    for j=0 upto n-1:
      if odd(i+j):
        for k=0 step u/5 until u:
          draw ( (k,0)--(u,u-k) )
               shifted (i*u,j*u);
          draw ( (0,k)--(u-k,u) )
               shifted (i*u,j*u);
        endfor;
      fi;
    endfor;
  endfor;
  for i=0 upto n:
    draw (0,i*u)--(n*u,i*u);
    draw (i*u,0)--(i*u,n*u);
  endfor;
endfig;
end;
