input plain;
beginfig(75)
  pair A,B,C,D,E;
  A := (1cm,0);
  B := A rotated 72;
  C := B rotated 72;
  D := C rotated 72;
  E := D rotated 72;
  draw A--B--C--D--E--cycle;
endfig;
end;
