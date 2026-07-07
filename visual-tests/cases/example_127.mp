input plain;
beginfig(127)
  u:=1cm;
  draw (-2u,0)--(2u,0);
  draw (0,-2u)--(0,2u);
  for i=-2u step u until 2u:
    draw (i,2u)--(i,-2u);
    draw (2u,i)--(-2u,i);
  endfor;
  for i=-2u step u/5 until 2u:
    draw (i,2u)--(i,-2u) withpen pencircle scaled .2bp;
    draw (2u,i)--(-2u,i) withpen pencircle scaled .2bp;
  endfor;
endfig;
end;
