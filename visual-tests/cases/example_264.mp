input plain;
input boxes;
beginfig(264)
  boxit.a(btex A etex);
  boxit.b(btex B etex);
  boxit.c(btex C etex);
  boxit.d(btex D etex);
  boxit.e(btex E etex);

  d.c = 1cm*up;
  e.c = 1cm*up rotated (1*72);
  a.c = 1cm*up rotated (2*72);
  b.c = 1cm*up rotated (3*72);
  c.c = 1cm*up rotated (4*72);

  drawunboxed(a,b,c,d,e);

  drawarrow a.c -- b.c cutbefore bpath.a cutafter bpath.b;
  drawarrow b.c -- c.c cutbefore bpath.b cutafter bpath.c;
  drawarrow c.c -- d.c cutbefore bpath.c cutafter bpath.d;
  drawarrow d.c -- e.c cutbefore bpath.d cutafter bpath.e;
  drawarrow e.c -- a.c cutbefore bpath.e cutafter bpath.a;
endfig;
end;
