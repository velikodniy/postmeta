input plain;
input boxes;
vardef TEX primary s = s infont defaultfont scaled defaultscale enddef;
beginfig(253)
  vardef boxTEX expr s =
    save p,h,l;
    picture p;
    numeric h,l;
    p := TEX(s);
    h := max(ypart ulcorner(p), abs(ypart llcorner(p)));
    l := xpart lrcorner(p);
    setbounds p to (0,-h)--(l,-h)--(l,h)--(0,h)--cycle;
    p
  enddef;

  draw (0,0) -- (5cm,0) withcolor red;
  boxjoin(b.c - a.c = (1cm,0));
  boxit a (boxTEX "a");
  boxit b (boxTEX "b");
  boxit c (boxTEX "c");
  boxit d (boxTEX "d");
  boxit e (boxTEX "e");
  drawunboxed(a,b,c,d,e);
endfig;
end;
