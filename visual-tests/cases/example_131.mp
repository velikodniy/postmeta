input plain;
beginfig(131)
  transform T;
  u:=1cm;
  z1=(0,2u);
  n := 5;
  for i=1 upto n-1:
    z[i+1] = z1 rotated (360*i/n);
  endfor;
  z1 transformed T = .1[z1,z2];
  z2 transformed T = .1[z2,z3];
  z3 transformed T = .1[z3,z4];
  path p;
  p = for i=1 upto n: z[i] -- endfor cycle;
  for i=0 upto 100:
    fill p withcolor .8*white;
    p := p transformed T;
    fill p withcolor white;
    p := p transformed T;
  endfor;
endfig;
end;
