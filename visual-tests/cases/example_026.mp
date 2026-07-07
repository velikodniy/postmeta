input plain;
beginfig(26)
  pair A, B, C, D;
  A:=(-1.5cm,-1.5cm); B:=(1.5cm,-1.5cm);
  C:=(1.5cm,1.5cm);   D:=(-1.5cm,1.5cm);
  fill A--C--B--D--cycle withcolor .8white;
  draw (-1.5cm,0)--(1.5cm,0);
  draw (0,-1.5cm)--(0,1.5cm);
  drawarrow (0,0)--(1cm,0)
            withpen pencircle scaled 2bp;
  drawarrow (0,0)--(0,1cm)
            withpen pencircle scaled 2bp;
endfig;
end;
