input plain;
beginfig(5)
  pair A, B, C;
  A:=(0,0); B:=(1cm,0); C:=(0,1cm);
  draw A--B--C--cycle;
  draw A withpen pencircle scaled 4bp;
  draw B withpen pencircle scaled 4bp;
  draw C withpen pencircle scaled 4bp;
endfig;
end;
