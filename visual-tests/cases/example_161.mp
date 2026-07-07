input plain;
beginfig(161)
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

  vardef milieu_time(expr p) =
    save l,i,tot,A,B,t;
    numeric l,tot,i,t;
    pair A,B;
    tot := longueur(p);
    l:=0;
    B := point 0 of p;
    for i:=0 step .01 until length(p):
      t:=i;
      A := B;
      B := point i of p;
      l := l+abs(B-A);
      exitif l > 1/2 tot;
    endfor;
    t
  enddef;

  save arrowhead;
  vardef arrowhead expr p =
    save A,B,u; pair A,B,u;
    A := milieu(p);
    B := p intersectionpoint
         (fullcircle scaled ahlength shifted A);
    u := unitvector(direction milieu_time(p) of p);
    A -- (A - ahlength*u rotated 30) -- B --
    (A - ahlength*u rotated -30) -- cycle
  enddef;

  u:=1cm;
  drawarrow (0,0) .. (-u,u) .. (u,u);
endfig;
end;
