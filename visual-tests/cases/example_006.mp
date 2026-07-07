input plain;
beginfig(6)
  pair A, B, C, D;
  A:=(0,0); B:=(1cm,0);
  C:=(1cm,1cm); D:=(0,1cm);
  draw A--B--C--D--cycle;
  draw A--C;
  draw B--D;
  draw A withpen pencircle scaled 4bp;
  draw B withpen pencircle scaled 4bp;
  draw C withpen pencircle scaled 4bp;
  draw D withpen pencircle scaled 4bp;
endfig;
end;
