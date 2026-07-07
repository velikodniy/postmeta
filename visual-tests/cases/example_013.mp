input plain;
beginfig(13)
  pair A, B, C;
  A:=(0,0); B:=(1cm,0); C:=(0,1cm);
  draw A--B--C--cycle;
  draw 1/2[A,B] -- C dashed evenly;
  draw 1/2[B,C] -- A dashed evenly;
  draw 1/2[C,A] -- B dashed evenly;
  draw 1/3 A + 1/3 B + 1/3 C
       withpen pencircle scaled 4bp
       withcolor red;
endfig;
end;
