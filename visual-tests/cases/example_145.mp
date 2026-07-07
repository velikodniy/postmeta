input plain;
beginfig(145)
  u:=1cm;
  def couleur(expr c) = c*white enddef;
  vardef degrade(expr p,q,M,N) =
    save a,b;
    numeric a,b;
    a := length(p);
    b := length(q);
    for i=0 upto M:
      draw (i/M) [ point 0 of p, point 0 of q ]
      for j=1 upto N:
        .. (i/M) [ point (j/N*a) of p, point (j/N*b) of q ]
      endfor
      withcolor couleur(i/M);
    endfor;
  enddef;
  degrade(
    (-.5u,-.5u) .. (.5u,.5u) .. cycle,
    (-u,-u) -- (u,-u) -- (u,u) -- (-u,u) -- cycle,
    255,
    100);
endfig;
end;
