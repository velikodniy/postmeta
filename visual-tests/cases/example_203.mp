input plain;
beginfig(203)
  pair A,B,C,D;
  u := 3cm;
  A := (0,0);
  B := (u,0);
  D := B rotated 72;
  C := (u,0) + D;
  draw A--B--C--D--cycle;
  draw A--C;
  draw btex $B'$ etex shifted 1/3 (A+B+C);
  draw btex $B$ etex shifted 1/3 (A+D+C);

endfig;
end;
