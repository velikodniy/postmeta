input plain;
beginfig(23)
  pair A, B, C;
  A:=(0,0); B:=(1cm,0); C:=(0,1cm);
  draw A--B--C--cycle withpen pencircle scaled 2bp;
  fill A--B--C--cycle withcolor .8 white;
endfig;
end;
