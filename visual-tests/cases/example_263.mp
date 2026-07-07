input plain;
input boxes;
beginfig(263)
  boxit.a(btex A etex);
  boxit.b(btex B etex);
  boxit.c(btex C etex);
  boxit.d(btex D etex);
  boxit.e(btex E etex);

  b.c-a.c = (1cm,0);
  c.c-b.c = (b.c-a.c) rotated 72;
  d.c-c.c = (c.c-b.c) rotated 72;
  e.c-d.c = (d.c-c.c) rotated 72;
  a.c-e.c = (e.c-d.c) rotated 72;
  b.c-a.c = (a.c-e.c) rotated 72;

  drawboxed(a,b,c,d,e);

  drawarrow a.c -- b.c cutbefore bpath.a cutafter bpath.b;
  drawarrow b.c -- c.c cutbefore bpath.b cutafter bpath.c;
  drawarrow c.c -- d.c cutbefore bpath.c cutafter bpath.d;
  drawarrow d.c -- e.c cutbefore bpath.d cutafter bpath.e;
  drawarrow e.c -- a.c cutbefore bpath.e cutafter bpath.a;
endfig;
end;
