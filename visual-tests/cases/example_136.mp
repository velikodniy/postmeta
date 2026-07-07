input plain;
beginfig(136)
  numeric n; n:=5;
  pair O,A,B,C,D;
  O = (0,0);
  A = 1cm*up;
  B = 2cm*up rotatedabout(A,30);
  C = 2cm*up;
  D = 2cm*up rotatedabout(A,-30);
  for i=0 upto n-1:
    draw (O--A--C) rotated (i*360/n);
    draw (B--A--D) rotated (i*360/n);
    draw A rotated (i*360/n) withpen pencircle scaled 4bp;
    draw B rotated (i*360/n) withpen pencircle scaled 4bp;
    draw C rotated (i*360/n) withpen pencircle scaled 4bp;
    draw D rotated (i*360/n) withpen pencircle scaled 4bp;
  endfor;
  draw O withpen pencircle scaled 4bp;
endfig;
end;
