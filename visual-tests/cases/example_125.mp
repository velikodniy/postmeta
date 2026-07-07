input plain;
beginfig(125)
  u:=1cm;
  draw (-2u,0)--(2u,0);
  draw (0,-2u)--(0,2u);
  for i=-2u step u until 2u:
    draw (i,u/10)--(i,-u/10);
    draw (u/10,i)--(-u/10,i);
  endfor;
  for i=-2u step u/5 until 2u:
    draw (i,u/20)--(i,-u/20);
    draw (u/20,i)--(-u/20,i);
  endfor;
endfig;
end;
