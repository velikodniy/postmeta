input plain;
beginfig(123)
  path p;
  p = (0,0) .. (-1cm,2cm) .. (2cm,1cm) .. (1cm,0);
  draw p;
  n:=10;
  for i=0 step length(p)/n until length(p):
    drawarrow (point i of p) --
              1cm * unitvector(direction i of p)
              shifted point i of p;
  endfor;
endfig;
end;
