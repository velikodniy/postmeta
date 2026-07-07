input plain;
beginfig(206)
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
  A := A;
  B := C;
  C := D;
        E := (d1/(d0+d1)) [A,C];
        F := (d0/(d0+d2)) [A,B];
  B := 3*(C-E);
  C := 3*(F-E);

  draw A--B--C--cycle;

  D := (d0/(d0+d2)) [C,A];
  draw B--C--D--cycle;
  draw btex $A$ etex shifted 1/3(B+C+D);
  draw B--D--A--cycle;
  draw btex $B'$ etex shifted 1/3(B+D+A);
endfig;
end;
