input plain;
beginfig(164)
  pair A,B,C;
  C = 3mm*up;
  A = C rotated 120;
  B = C rotated -120;
  picture pic ;
  pic:=nullpicture;
  addto pic doublepath A--B--C--cycle withpen currentpen;
  addto pic doublepath A withpen pencircle scaled 4bp;
  addto pic doublepath B withpen pencircle scaled 4bp;
  addto pic doublepath C withpen pencircle scaled 4bp;
  for i=-3 upto 3:
    for j=-3 upto 3:
      draw pic shifted( i*(B-A) + j*(C-A) );
    endfor;
  endfor;
  clip currentpicture to (-2cm,-2cm)--(2cm,-2cm)--(2cm,2cm)--(-2cm,2cm)--cycle;
endfig;
end;
