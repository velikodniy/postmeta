input plain;
beginfig(156)
  u:=1cm;
  vardef random_path (expr n) =
    save i, A ; numeric i; pair A[];
    for i=0 upto n:
      A[i] = (uniformdeviate(2u), uniformdeviate(2u));
    endfor;
    A[0]
    for i=1 upto n:
      .. A[i]
    endfor
  enddef;

  vardef intersections(expr p,q) =
    save a,b,N,i,j;
    numeric N,i,j;
    N:=10;
    for i=0 step length(p)/N until length(p):
      for j=0 step length(q)/N until length(p):
        numeric a,b;
        pair A;
        (a,b) = (subpath(i,i+length(p)/N) of p)
                intersectiontimes
                (subpath(j,j+length(q)/N) of q);
        if a <> -1:
          A = point a of subpath(i,i+length(p)/N) of p;
          show A;
          draw A withpen pencircle scaled 4bp;
        fi;
      endfor;
    endfor;
  enddef;

  path p,q;
  p:=random_path(4);
  q:=random_path(4);
  draw p withcolor red;
  draw q withcolor blue;
  intersections(p,q);
endfig;
end;
