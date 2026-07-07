input plain;
beginfig(97)
  path c[], l[];
  c[0] = fullcircle xscaled 1cm yscaled .5cm
         shifted (0,1cm);
  c[1] = c[0] rotated 120;
  c[2] = c[1] rotated 120;
  pair A;
  A = (-.5cm,1cm);
  l[0] = A{down} ..
         (A xscaled -1 rotated 120){-down rotated 120};
  l[1] = l[0] rotated 120;
  l[2] = l[1] rotated 120;
  draw c[0]; draw c[1]; draw c[2];
  draw l[0]; draw l[1]; draw l[2];
endfig;
end;
