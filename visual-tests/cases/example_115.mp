input plain;
beginfig(115)
  pair A,B;
  path p;
  A = (0,1cm);
  B = A rotated 120;
  p = A{dir 0} .. tension 2 .. B{dir 120};
  numeric a;
  (a,whatever) = p intersectiontimes (p rotated 120);
  draw subpath(0,a-.02) of p;
  draw subpath(a+.02,1) of p;
  draw subpath(0,a-.02) of p rotated 120;
  draw subpath(a+.02,1) of p rotated 120;
  draw subpath(0,a-.02) of p rotated -120;
  draw subpath(a+.02,1) of p rotated -120;
endfig;
end;
