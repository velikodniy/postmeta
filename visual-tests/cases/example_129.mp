input plain;
beginfig(129)
  transform T;
  u:=1cm;
  z0=(0,0); z1=(2u,0); z3 = z1 rotated 90; z2 = z1+z3;
  z0 transformed T = .1[z0,z1];
  z1 transformed T = .1[z1,z2];
  z2 transformed T = .1[z2,z3];
  path p;
  p = z0--z1--z2--z3--cycle;
  fill p withcolor .8*white;
  fill p transformed T withcolor white;
endfig;
end;
