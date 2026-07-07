input plain;
input boxes;
beginfig(268)
  def drawcoloredboxed(expr c)(text t) =
    forsuffixes a=t:
      fill bpath a withcolor c;
    endfor;
    drawboxed(t);
  enddef;

  circleit.a(btex Start etex);
  a.c = (0,0);
  a.dx = a.dy;
  circleit.b(btex End etex);
  b.c = (2cm,0);
  b.dx = b.dy;
  drawcoloredboxed(.5[red,white],  a);
  drawcoloredboxed(.5[blue,white], b);
  drawarrow  a.c {dir 45} .. b.c {dir -45}
  cutbefore bpath.a cutafter bpath.b;
  drawarrow  b.c {dir -135} .. a.c {dir 135}
  cutbefore bpath.b cutafter bpath.a;

endfig;
end;
