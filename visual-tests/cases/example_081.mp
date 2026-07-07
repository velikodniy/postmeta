input plain;
beginfig(81)
  pair A,B,C,AA,BB,CC,H;
  A=(0,0); B=(3cm,0); C=(1cm,2cm);
  AA - A = whatever * (B-C) rotated 90;
  AA = whatever [B,C];
  BB - B = whatever * (A-C) rotated 90;
  BB = whatever [A,C];
  CC - C = whatever * (A-B) rotated 90;
  CC = whatever [A,B];
  H = whatever [A,AA];
  H = whatever [B,BB];
  draw A--B--C--cycle;
  draw A--AA;
  draw B--BB;
  draw C--CC;
  draw H withpen pencircle scaled 4bp;
endfig;
end;
