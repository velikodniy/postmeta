input plain;
beginfig(124)
  u:=1cm;
  draw (-2u,0)--(2u,0);
  draw (0,-2u)--(0,2u);
  for i=-2u step u until 2u:
    draw (i,u/20)--(i,-u/20);
    draw (u/20,i)--(-u/20,i);
  endfor;
endfig;
end;
