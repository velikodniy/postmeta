input plain;
input boxes;
beginfig(265)
  def linkboxes(suffix a,b) =
    drawarrow a.c -- b.c cutbefore bpath.a cutafter bpath.b;
  enddef;

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

  linkboxes(a,b);
  linkboxes(b,c);
  linkboxes(c,d);
  linkboxes(d,e);
  linkboxes(e,a);
endfig;
end;
