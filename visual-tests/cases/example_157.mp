input plain;
beginfig(157)
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

  vardef auto_intersections(expr p) =
    save a,b,N,i,j;
    numeric N,i,j;
    N:=100;
    for i=0 step length(p)/N until length(p):
      for j=i+2*length(p)/N
          step length(p)/N
          until length(p):
        numeric a,b;
        pair A;
        (a,b) = (subpath(i,i+length(p)/N) of p)
                intersectiontimes
                (subpath(j,j+length(p)/N) of p);
        if a <> -1:
          A = point a of subpath(i,i+length(p)/N) of p;
          show A;
          draw A withpen pencircle scaled 4bp;
        fi;
      endfor;
    endfor;
  enddef;

  u:=2cm;
  path p,q;
  p:=random_path(12);
  draw p;
  auto_intersections(p);
endfig;
end;
