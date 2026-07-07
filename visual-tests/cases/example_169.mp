input plain;
beginfig(169)
  path p;
  p  = fullcircle scaled 2cm;
  z0 = (-1cm,0);
  draw p;
  draw z0 withpen pencircle scaled 2pt;

  pair A[];
  for i=0 step length(p)/100 until length(p):
    pair M,N;
    M = point i of p;
    N-M = whatever * direction i of p;
    N-z0 = whatever * direction i of p rotated 90;
    A[i] := N;
  endfor;
  draw for i=0 step length(p)/100 until length(p):
    A[i] ..
  endfor cycle;
endfig;
end;
