input plain;
beginfig(8)
  pair A, B, C;
  A:=(0,0); B:=(1cm,0); C:=(0,1cm);
  draw A--B--C--cycle;
  draw 1/2[A,B] -- C;
  draw 1/2[B,C] -- A;
  draw 1/2[C,A] -- B;
  draw 1/3 A + 1/3 B + 1/3 C
       withpen pencircle scaled 4bp;
endfig;
end;
