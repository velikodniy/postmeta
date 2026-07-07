input plain;
beginfig(195)
  n:=8;
  u:=5mm;
  for i=0 upto n-1:
    for j=0 upto n-1:
      if odd(i+j):
        for k=0 step u/5 until 4/5 u:
          if odd(k*5/u):
            fill ( (k,0)--(u,u-k)--(u,u-k-u/5)--
                   (k+u/5,0)--cycle )
                 shifted (i*u,j*u) withcolor .8white;
          else:
            fill ( (0,k)--(u-k,u)--(u-k-u/5,u)--
                   (0,k+u/5)--cycle )
                 shifted (i*u,j*u) withcolor .8white;
          fi;
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
