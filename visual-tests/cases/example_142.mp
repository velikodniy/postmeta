input plain;
beginfig(142)
  z0 = (50,50);
  z1 = z0 rotated 90;
  z2 = z1 rotated 90;
  z3 = z2 rotated 90;
  path carre;
  carre = z0--z1--z2--z3--cycle;
  s := .01;
  path rect;
  z4 = s [z2,z3]; z5 = s [z1,z0];
  rect = z1--z2--z4--z5--cycle;
  for i=0 step s until 1:
    fill rect shifted (i*(z0-z1)) withcolor i*white;
  endfor;
  draw carre withpen pencircle scaled 2bp;
endfig;
end;
