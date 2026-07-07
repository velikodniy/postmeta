input plain;
beginfig(109)
  u:=1cm;
  path a,b,c,d;
  a = (-u,-.2u){up} .. tension 1.2 .. (u,-.2u){down};
  b = a rotated 90;
  c = b rotated 90;
  d = c rotated 90;
  fill buildcycle(a,b,c,d) withcolor .8white;
  draw a; draw b; draw c; draw d;

endfig;
end;
