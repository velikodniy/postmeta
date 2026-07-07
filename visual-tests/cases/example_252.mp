input plain;
input boxes;
beginfig(252)
  draw (0,0) -- (5cm,0) withcolor red;
  boxjoin(b.c - a.c = (1cm,0));
  boxit a (btex a etex);
  boxit b (btex b etex);
  boxit c (btex c etex);
  boxit d (btex d etex);
  boxit e (btex e etex);
  drawunboxed(a,b,c,d,e);
endfig;
end;
