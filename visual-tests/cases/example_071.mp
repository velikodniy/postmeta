input plain;
beginfig(71)
  pair A,B,C,AA,BB,CC,G;
  A=(0,0); B=(3cm,0); C=(1cm,2cm);
  AA = 1/2 [B,C];
  BB = 1/2 [C,A];
  CC = 1/2 [A,B];
  G = whatever [A,AA];
  G = whatever [B,BB];
  draw A--B--C--cycle;
  draw A--AA dashed withdots;
  draw B--BB dashed withdots;
  draw C--CC dashed withdots;
  draw G withpen pencircle scaled 4bp;
endfig;
end;
