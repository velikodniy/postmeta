input plain;
beginfig(211)
  u:=2cm;
  pickup pencircle scaled 1pt;
  for i=0 upto 500:
    draw (u*uniformdeviate(1), u*uniformdeviate(1));
  endfor;
endfig;
end;
