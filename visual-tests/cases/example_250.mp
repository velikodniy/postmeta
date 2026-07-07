input plain;
input boxes;
beginfig(250)
  boxjoin(a.se = b.sw; a.ne = b.nw);
  boxit.a1(btex a etex);
  boxit.a2(btex b etex);
  boxit.a3(btex c etex);
  boxit.a4(btex d etex);
  drawboxed(a1,a2,a3,a4);
endfig;
end;
