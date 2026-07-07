input plain;
beginfig(221)
  vardef barycentre(text t) =
    save n, G;
    pair G; numeric n;
    G := origin; n:=0;
    for a=t:
      G:=G+a;
      n:=n+1;
    endfor;
    G/n
  enddef;

  pair A[];
  n:=10;
  for i=0 upto n:
    A[i] = 1cm*(normaldeviate, normaldeviate);
    draw A[i] withpen pencircle scaled 4bp;
  endfor;
  draw barycentre(A[0] for i=1 upto 10: ,A[i] endfor)
    withpen pencircle scaled 4bp withcolor red;
endfig;
end;
