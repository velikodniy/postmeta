input plain;
beginfig(96)
  pair A,B;
  path p;
  numeric n;
  n:=5;
  A = (0,1cm);
  B = A rotated (2*360/n);
  p = A{dir 180} .. tension 4 .. B{dir (180+2*360/n)};
  draw p withcolor red;
  draw p rotated (1*360/n);
  draw p rotated (2*360/n);
  draw p rotated (3*360/n);
  draw p rotated (4*360/n);
endfig;
end;
