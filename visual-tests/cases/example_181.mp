input plain;
beginfig(181)
  save arrowhead;
  vardef arrowhead expr p =
    save A,B,u; pair A,B,u;
    A := point length(p) of p;
    B := p intersectionpoint
         (fullcircle scaled ahlength shifted A);
    u := unitvector(direction length(p) of p);
    A -- (A - ahlength*u rotated 30) -- B --
    (A - ahlength*u rotated -30) -- cycle
  enddef;

  u:=1cm;
  drawarrow (0,0) .. (-u,u) .. (u,u);
endfig;
end;
