input plain;
input boxes;
beginfig(260)
  draw (0,0) -- (5cm,0) withcolor red;
  picture p;
  numeric h;
  p := btex b etex;
  h = ypart ( ulcorner p - llcorner p );
  boxjoin(
    b.c - a.c = (1cm,0);
    ypart( b.ne - a.ne ) = 0;
    ypart( a.ne - a.se ) = h+2defaultdy;
  );
  boxit a (btex a etex);
  boxit b (btex b etex);
  boxit c (btex c etex);
  boxit d (btex d etex);
  boxit e (btex e etex);
  drawboxed(a,b,c,d,e);
endfig;
end;
