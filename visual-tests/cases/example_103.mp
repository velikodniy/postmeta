input plain;
beginfig(103)
  pair A,AA,B,BB,C,CC,O,H;
  A=(0,0); B=(3cm,0); C=(1cm,2cm);
  AA = 1/2[B,C];
  BB = 1/2[A,C];
  CC = 1/2[A,B];
  O - 1/2[BB,CC] = whatever * (BB-CC) rotated 90;
  O - 1/2[AA,BB] = whatever * (AA-BB) rotated 90;
  draw A--B--C--cycle;
  draw AA withpen pencircle scaled 4bp;
  draw BB withpen pencircle scaled 4bp;
  draw CC withpen pencircle scaled 4bp;
  draw fullcircle scaled 2abs(O-AA) shifted O;
  % Il faut aussi tracer les hauteurs
  pair AA,BB,CC;
  AA - A = whatever * (B-C) rotated 90;
  AA = whatever [B,C];
  BB - B = whatever * (A-C) rotated 90;
  BB = whatever [A,C];
  CC - C = whatever * (A-B) rotated 90;
  CC = whatever [A,B];
  draw A--AA; draw B--BB; draw C--CC;
  draw AA withpen pencircle scaled 4bp;
  draw BB withpen pencircle scaled 4bp;
  draw CC withpen pencircle scaled 4bp;
  % Il passe aussi par le milieu de HA, HB, HC
  H = whatever [A,AA];
  H = whatever [B,BB];
  draw 1/2 [A,H] withpen pencircle scaled 4bp;
  draw 1/2 [B,H] withpen pencircle scaled 4bp;
  draw 1/2 [C,H] withpen pencircle scaled 4bp;
endfig;
end;
