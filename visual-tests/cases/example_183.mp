input plain;
beginfig(183)
  save arrowhead;
  vardef arrowhead expr p =
    save A,u,a,b; pair A,u; path a,b;
    A := point length(p) of p;
    u := unitvector(direction length(p) of p);
    a := A{-u} .. (A - ahlength*u rotated 30);
    b := A{-u} .. (A - ahlength*u rotated -30);
    ( a & reverse(a) & b & reverse(b) ) --cycle
  enddef;

  u:=1cm;
  drawarrow (0,0) .. (-u,u) .. (u,u);
endfig;
end;
