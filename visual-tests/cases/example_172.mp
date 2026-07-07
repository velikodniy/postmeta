input plain;
beginfig(172)
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
  p := (-1cm,0) .. (1cm,-1cm) .. (8mm,0)
       .. (1cm,1cm) .. (-1cm,1cm) .. cycle;
  z0 = (-2cm,0);
  draw p withpen pencircle scaled 1bp;
  draw z0 withpen pencircle scaled 3pt;
  draw cardiodide(p,z0);
endfig;
end;
