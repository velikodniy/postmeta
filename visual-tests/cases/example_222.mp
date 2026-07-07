input plain;
beginfig(222)
  vardef barycentre(text t) =
    save a, i, n, G, X;
    pair G,X; numeric n,i;
    G := origin; n:=0; i:=0;
    for a=t:
      show("i = "& decimal(i));
      show a;
      if odd(i):
        show("odd");
        n:=n+a;
        G:= G + a*X;
      else:
        show("even");
        X:=a;
      fi;
      i:=i+1;
    endfor;
    G/n
  enddef;

  pair A[];
  n:=10;
  for i=0 upto n:
    A[i] = 1cm*(normaldeviate, normaldeviate);
    draw A[i] withpen pencircle scaled 4bp;
  endfor;
  draw barycentre(A[0],0 for i=1 upto 10: ,A[i],i endfor)
    withpen pencircle scaled 4bp withcolor red;
endfig;
end;
