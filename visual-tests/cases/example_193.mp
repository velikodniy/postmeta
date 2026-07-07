input plain;
beginfig(193)
  n:=8;
  u:=5mm;
  for i=0 upto n-1:
    for j=0 upto n-1:
      if odd(i+j):
        fill (0,0)--(u,0)--(u,u)--(0,u)--cycle
             shifted (i*u,j*u) withcolor .8white;
      fi;
    endfor;
  endfor;
  for i=0 upto n:
    draw (0,i*u)--(n*u,i*u);
    draw (i*u,0)--(i*u,n*u);
  endfor;
endfig;
end;
