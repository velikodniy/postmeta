input plain;
beginfig(143)
  z0 = (50,50);
  z1 = z0 rotated 90;
  z2 = z1 rotated 90;
  z3 = z2 rotated 90;
  path carre;
  carre = z0--z1--z2--z3--cycle;
  s := .01;
  for i=1 step -s until s:
    fill carre scaled i withcolor i*white;
  endfor;
endfig;
end;
