input plain;
beginfig(152)
  u:=5mm;
  vardef project(expr x,y,z) =
    x*(-1,-1) + y*(1,0) + z*(0,1)
  enddef;
  vardef f(expr x,y) = sind(x/u*180)*sind(y/u*180)*u enddef;
  numeric m,M;
  m:=-2u; M:=2u;
  for i=m step .1u until M:
    path p;
    p =
      for j=m step .1u until M:
        project(i,j,f(i,j)) --
      endfor
      project(i,M,f(i,M));
    fill (project(i,m,f(i,m)) - (0,3u)) -- p --
         (project(i,M,f(i,M)) - (0,3u)) -- cycle
         withcolor white;
    draw (project(i,m,f(i,m)) - (0,3u)) -- p --
         (project(i,M,f(i,M)) - (0,3u)) -- cycle;
    draw p;
  endfor;
endfig;
end;
