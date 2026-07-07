input plain;
beginfig(171)
vardef cardiodide(expr p, O) =
  save i,M,N;
  numeric i;
  for i=0 step length(p)/100 until length(p):
    hide(
      pair M,N;
      M = point i of p;
      N-M = whatever * direction i of p;
      N-O = whatever * direction i of p rotated 90;
    )
    N ..
  endfor cycle
enddef;

  path p;
  p  = fullcircle scaled 2cm;
  z0 = (-1cm,0);
  pickup pencircle scaled 1pt
  draw p;
  draw z0 withpen pencircle scaled 3pt;
  draw cardiodide(p,z0);
  pickup pencircle scaled .4pt
  pair M,N;
  i:=1.5;
  M = point i of p;
  N-M  = whatever * direction i of p;
  N-z0 = whatever * direction i of p rotated 90;
  draw z0--N;
  draw (-1/2)[N,M]--(3/2)[N,M];
  draw N withpen pencircle scaled 3pt;
  draw M withpen pencircle scaled 3pt;
endfig;
end;
