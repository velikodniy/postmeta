input plain;
input boxes;
vardef TEX primary s = s infont defaultfont scaled defaultscale enddef;
vardef boxTEX expr s = TEX(s) enddef;
beginfig(254)
  draw (0,0) -- (5cm,0) withcolor red;
  boxjoin(b.c - a.c = (1cm,0));
  boxit a (boxTEX "a");
  boxit b (boxTEX "b");
  boxit c (boxTEX "c");
  boxit d (boxTEX "d");
  boxit e (boxTEX "e");
  drawboxed(a,b,c,d,e);
endfig;
end;
