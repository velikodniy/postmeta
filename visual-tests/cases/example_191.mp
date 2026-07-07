input plain;
vardef TEX primary s = s infont defaultfont scaled defaultscale enddef;
beginfig(191)
  vardef mylabel(expr pic, p, t) =
    save A; pair A;
    A = point t of p +
        8bp * unitvector(direction t of p) rotated 90;
    label(pic, A);
  enddef;
  path p; u:=1cm;
  p = (0,0)..(-u,u)..(u,u);
  draw p;
  for i=0 step .2 until length(p):
    draw point i of p withpen pencircle scaled 4bp;
    mylabel(TEX decimal(i),p,i);
  endfor;
endfig;
end;
