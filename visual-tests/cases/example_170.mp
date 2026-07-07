input plain;
beginfig(170)
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
  draw p;
  draw z0 withpen pencircle scaled 2pt;
  draw cardiodide(p,z0);
endfig;
end;
