input plain;
input boxes;
beginfig(266)
  boxit a(btex Test etex);
  fill bpath a withcolor .5[red,white];
  drawboxed(a);

endfig;
end;
