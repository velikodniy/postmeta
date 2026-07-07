input plain;
input boxes;
beginfig(246)
  boxjoin(
    a.dx = a.dy;
    b.dx = b.dy;
    a.e + (5mm,0) = b.w;
    );
  circleit.a(btex Start etex);
  a.c = (0,0);
  circleit.b(btex End etex);
  drawboxed(a,b);
  drawarrow  a.c {dir 45} .. b.c {dir -45}
  cutbefore bpath.a cutafter bpath.b;
  drawarrow  b.c {dir -135} .. a.c {dir 135}
  cutbefore bpath.b cutafter bpath.a;
endfig;
end;
