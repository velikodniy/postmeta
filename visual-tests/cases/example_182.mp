input plain;
beginfig(182)
  save arrowhead;
  vardef arrowhead expr p =
    save A,u; pair A,u;
    A := point length(p) of p;
    u := unitvector(direction length(p) of p);
    A -- (A - ahlength*u rotated 30) -- A --
    (A - ahlength*u rotated -30) -- cycle
  enddef;

  u:=1cm;
  drawarrow (0,0) .. (-u,u) .. (u,u);
endfig;
end;
