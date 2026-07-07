input plain;
beginfig(144)
  u:=1cm;
  vardef degrade(expr p,q,M,N) =
    save a,b;
    numeric a,b;
    a := length(p);
    b := length(q);
    for i=0 upto M:
      draw (i/M) [ point 0 of p, point 0 of q ]
      for j=1 upto N:
        .. (i/M) [ point (j/N*a) of p, point (j/N*b) of q ]
      endfor;
    endfor;
  enddef;
  degrade(
    (-.1u,-.1u) .. (.1u,.1u) .. cycle,
    (-u,-u) -- (u,-u) -- (u,u) -- (-u,u) -- cycle,
    10,
    100);
endfig;
end;
