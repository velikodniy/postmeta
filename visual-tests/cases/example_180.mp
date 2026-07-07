input plain;
beginfig(180)
  save arrowhead;
  vardef arrowhead expr p =
    save A,u; pair A,u;
    A := point length(p) of p;
    u := unitvector(direction length(p) of p);
    A -- (A - ahlength*u rotated 15) --
    (A - ahlength*u rotated -15) -- cycle
  enddef;

  u:=1cm;
  drawarrow (0,0) .. (-u,u) .. (u,u);
endfig;
end;
