input plain;
beginfig(166)
  ux:=2mm;
  uy:=5mm;
  numeric xmin, xmax, ymin, ymax, M;
  xmin := -6.3; xmax := 12.6;
  ymin := -2;   ymax := 2;
  M := 100;
  draw (ux*xmin,0) -- (ux*xmax,0);
  draw (0,uy*ymin) -- (0,uy*ymax);
  pair a[];
  for i=0 upto M:
    a[i] := (
      xmin + (i/M)*(xmax-xmin),
      sind(180/3.14*( xmin + (i/M)*(xmax-xmin) ))
    ) xscaled ux yscaled uy;
  endfor;
  draw a[0] for i=1 upto M: --a[i] endfor;
endfig;
end;
