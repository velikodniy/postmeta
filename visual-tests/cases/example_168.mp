input plain;
beginfig(168)
  ux:=5mm;
  uy:=5mm;
  numeric xmin, xmax, ymin, ymax, M;
  xmin := .2; xmax := 3;
  ymin := -1.6;   ymax := 1.2;
  M := 100;
  draw (ux*-.1,0) -- (ux*xmax,0);
  draw (0,uy*ymin) -- (0,uy*ymax);
  pair a[];
  for i=0 upto M:
    a[i] := (
      xmin + (i/M)*(xmax-xmin),
      (1/256)*mlog(( xmin + (i/M)*(xmax-xmin) ))
    ) xscaled ux yscaled uy;
  endfor;
  draw a[0] for i=1 upto M: --a[i] endfor;
endfig;
end;
