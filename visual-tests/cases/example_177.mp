input plain;
beginfig(177)
  vardef bar(expr m,a,b,c) =
    m = 1/3a + 1/3b + 1/3c
  enddef;
  vardef dbar(expr m,a,b,c) =
    draw m--a; draw m--b; draw m--c;
    draw m withpen pencircle scaled 4bp;
  enddef;

  pair P[], A,B,C;
  for i=0 upto 4:
    P[i] = 1cm * up rotated (i*360/5);
    draw P[i] withpen pencircle scaled 4bp;
  endfor;
  bar(A, P[0], P[4], B);
  bar(B, A,    P[1], C);
  bar(C, B,    P[2], P[3]);
  draw fullcircle scaled 2cm dashed evenly;
  dbar(A, P[0], P[4], B);
  dbar(B, A,    P[1], C);
  dbar(C, B,    P[2], P[3]);
endfig;
end;
