input plain;
beginfig(146)
  def degrade(expr p, q, N) =
    begingroup
      save n, m, M;
      numeric n, m, M;
      n := length(p);
      m := length(q);
      M := n*m; % Il faudrait prendre le ppcm
      for i=0 upto N:
        draw
        (i/N)[ point 0 of p, point 0 of q ]
        { (i/N)[ direction 0 of p, direction 0 of q ] }
        for j=1 upto M-1:
          ..
          { (i/N) [ direction 1 of subpath((j-1)*n/M,j*n/M) of p,
                    direction 1 of subpath((j-1)*m/M,j*m/M) of q  ] }
          (i/N)[ point (j*n/M) of p, point (j*m/M) of q ]
          { (i/N) [ direction 0 of subpath(j*n/M,(j+1)*n/M) of p,
                    direction 0 of subpath(j*m/M,(j+1)*m/M) of q  ] }
        endfor
        ..
        { (i/N)[ direction n of p, direction m of q ] }
        (i/N)[ point n of p, point m of q ]
        ;
      endfor;
    endgroup;
  enddef;
  numeric u;
  u := 2cm;
  path p, q;
  p := fullcircle scaled u;
  q := (-u,-u)--(u,-u)--(u,u)--(-u,u)--cycle;
  degrade(p,q,10);
endfig;
end;
