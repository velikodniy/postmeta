input plain;
input boxes;
beginfig(258)
  draw (0,0) -- (5cm,0) withcolor red;
  boxjoin(b.c - a.c = (1cm,0); b.ne - b.se = a.nw - a.sw);
  boxit a (btex a etex);
  boxit b (btex b etex);
  boxit c (btex c etex);
  boxit d (btex d etex);
  boxit e (btex e etex);
  drawboxed(a,b,c,d,e);
endfig;
end;
