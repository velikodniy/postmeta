input plain;
beginfig(159)
  vardef longueur(expr p) = arclength(p) enddef;

  vardef milieu(expr p) =
    save l,i,tot,A,B;
    numeric l,tot,i;
    pair A,B;
    tot := longueur(p);
    l:=0;
    B := point 0 of p;
    for i:=0 step .01 until length(p):
      A := B;
      B := point i of p;
      l := l+abs(B-A);
      exitif l > 1/2 tot;
    endfor;
    1/2[A,B]
  enddef;

  path p;
  p := (0,0){up} .. (1cm,1cm) .. (1cm,0);
  draw p;
  draw point 1/2length(p) of p withpen pencircle scaled 4bp withcolor red;
  draw milieu(p) withpen pencircle scaled 4bp;
endfig;
end;
