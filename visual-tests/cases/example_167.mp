input plain;
beginfig(167)
  ux:=5mm;
  uy:=2mm;
  numeric xmin, xmax, ymin, ymax, M;
  xmin := -2; xmax := 2;
  ymin := -.1;   ymax := 8;
  M := 100;
  draw (ux*xmin,0) -- (ux*xmax,0);
  draw (0,uy*ymin) -- (0,uy*ymax);
  pair a[];
  for i=0 upto M:
    a[i] := (
      xmin + (i/M)*(xmax-xmin),
      mexp(256*( xmin + (i/M)*(xmax-xmin) ))
    ) xscaled ux yscaled uy;
  endfor;
  draw a[0] for i=1 upto M: --a[i] endfor;
endfig;
end;
