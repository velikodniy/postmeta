input plain;
input boxes;
beginfig(247)
  % Toujours mettre la commande boxjoin au d�but.
  boxjoin(a.e = b.w);
  boxit.a(btex A etex);
  boxit.b(btex B etex);
  boxit.c(btex C etex);
  boxit.d(btex D etex);
  drawboxed(a,b,c,d);
endfig;
end;
