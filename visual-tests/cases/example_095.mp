input plain;
beginfig(95)
  pair A,B;
  path p;
  A = (0,1cm);
  B = A rotated 120;
  p = A{dir 0} .. tension 2 .. B{dir 120};
  draw p;
  draw p rotated 120;
  draw p rotated -120;
endfig;
end;
