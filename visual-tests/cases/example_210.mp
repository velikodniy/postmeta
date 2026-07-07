input plain;
beginfig(210)
  u:=5mm;
  pickup pencircle scaled 1pt;
  for i=0 upto 500:
    draw (u*normaldeviate, u*normaldeviate);
  endfor;
endfig;
end;
