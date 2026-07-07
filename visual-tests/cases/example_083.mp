input plain;
beginfig(83)
  pair A,B,C,O;
  A=(0,0); B=(3cm,0); C=(1cm,2cm);
  O - 1/2[B,C] = whatever * (B-C) rotated 90;
  O - 1/2[A,B] = whatever * (A-B) rotated 90;
  draw A--B--C--cycle;
  draw O withpen pencircle scaled 4bp;
  draw fullcircle scaled 2abs(O-A) shifted O;
endfig;
end;
