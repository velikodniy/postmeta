input plain;
input boxes;
beginfig(249)
  boxjoin(a.se = b.sw; a.ne = b.nw);
  boxit.a(btex a etex);
  boxit.b(btex b etex);
  boxit.c(btex c etex);
  boxit.d(btex d etex);
  drawboxed(a,b,c,d);
endfig;
end;
