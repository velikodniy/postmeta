input plain;
beginfig(174)
  def curve(expr p,i,q,j,t) =
    point i of p {direction i of p} ..
    tension t ..
    point j of q {direction j of q}
  enddef;

  vardef sphere_with_holes (expr n) =
    save i;
    c[0] = fullcircle xscaled u yscaled 2u
                      shifted (4u,0) rotated (360/(2n)) ;
    draw c[0];
    for i=1 upto n-1:
      c[i] = c[i-1] rotated (360/n);
      draw c[i];
    endfor;
    l[0] = curve(c[0], 2, c[1], -2, 1);
    draw l[0];
    for i=1 upto n-1:
      l[i] = l[i-1] rotated (360/n);
      draw l[i];
    endfor;
  enddef;

  u:=3mm;
  path c[], l[];
  sphere_with_holes(5);
endfig;
end;
