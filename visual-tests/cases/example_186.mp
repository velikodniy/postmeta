input plain;
beginfig(186)
  save arrowhead;
  vardef arrowhead expr p =
    save A,u; pair A,u;
    A := point 1/2length(p) of p;
    u := unitvector(direction 1/2length(p) of p);
    A -- (A - ahlength*u rotated 30) -- A --
    (A - ahlength*u rotated -30) -- cycle
  enddef;

  u:=1cm;
  drawarrow (0,0) .. (-u,u) .. (u,u);
endfig;
end;
