input plain;
beginfig(126)
  u:=1cm;
  draw (-2u,0)--(2u,0);
  draw (0,-2u)--(0,2u);
  for i=-2u step u until 2u:
    draw (i,2u)--(i,-2u);
    draw (2u,i)--(-2u,i);
  endfor;
endfig;
end;
