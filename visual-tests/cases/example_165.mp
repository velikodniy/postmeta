input plain;
beginfig(165)
  pair A,B,C;
  C = 3mm*up;
  A = C rotated 120;
  B = C rotated -120;
  picture pic ;
  pic:=nullpicture;
  path p;
  p := A{(C-A) rotated 30} .. C{(C-A) rotated 30};
  addto pic doublepath p withpen currentpen;
  addto pic doublepath p rotated 120 withpen currentpen;
  addto pic doublepath p rotated -120 withpen currentpen;
  for i=-3 upto 3:
    for j=-3 upto 3:
      draw pic shifted( i*(B-A) + j*(C-A) );
    endfor;
  endfor;
  clip currentpicture to (-2cm,-2cm)--(2cm,-2cm)--(2cm,2cm)--(-2cm,2cm)--cycle;
endfig;
end;
