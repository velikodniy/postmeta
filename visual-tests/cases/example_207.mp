input plain;
beginfig(207)
  pair A,B,C,D,E,F;
  numeric d[];
  u := 3cm;
  A := (0,0);
  B := (u,0);
  D := B rotated 72;
  C := (u,0) + D;
  d[0] := 1;
  d[1] := sqrt( 2*(1+cosd(72)) );
  d[2] := sqrt( 2*(1-cosd(36)) );

  % B'
  E := (d1/(d0+d1)) [A,C];
  F := (d0/(d0+d2)) [A,B];

  % A'
  A := 2*(E-E);
  C := 2*(B-E);
  B := 2*(F-E);

  draw A--B--C--cycle;
  D := (d0/(d0+d2)) [A,B];
  draw C--D--B--cycle;
  draw btex $A'$ etex shifted 1/3(C+D+B);
  draw C--A--D--cycle;
  draw btex $B$ etex shifted 1/3(C+A+D);
endfig;
end;
