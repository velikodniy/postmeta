input plain;
beginfig(153)
  u:=1cm;
  vardef project(expr x,y,z) =
    x*(-1,-1) + y*(1,0) + z*(0,1)
  enddef;
  vardef f(expr x,y) = sind(x/u*180)*sind(y/u*180)*u enddef;
  m:=-2u; M:=2u; inc:=.1u;
  for i=m step inc until M:
    for j=m step inc until M:
      path p;
      p = project(i,j,f(i,j)) --
          project(i,j+inc,f(i,j+inc)) --
          project(i+inc,j+inc,f(i+inc,j+inc)) --
          project(i+inc,j,f(i+inc,j)) --
          cycle;
      fill p withcolor white;
      draw p;
    endfor
  endfor;
endfig;
end;
