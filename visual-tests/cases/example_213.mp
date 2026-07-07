input plain;
beginfig(213)
  m:=500;
  u:=1cm;
  pair A,B;
  A:=(0,0);
  for i=0 upto m:
    B:=(i/m*3u, (ypart A)+normaldeviate/m*30u);
    draw A--B;
    A:=B;
  endfor;
  draw (0,0)--(3u,0);
endfig;
end;
