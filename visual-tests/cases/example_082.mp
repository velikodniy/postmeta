input plain;
beginfig(82)
  pair A,B,C,H;
  A=(0,0); B=(3cm,0); C=(1cm,2cm);
  H - A = whatever * (B-C) rotated 90;
  H - B = whatever * (A-C) rotated 90;
  draw A--B--C--cycle;
  draw H withpen pencircle scaled 4bp;
endfig;
end;
