input plain;
beginfig(112)
    def compute_curve(suffix f)(expr xmin, xmax, xinc) =
    ( (xmin,f(xmin))
    for x=xmin+xinc step xinc until xmax:
      .. (x,f(x))
    endfor )
  enddef;
  vardef f(expr x) = x**2 + 1 enddef;
  vardef g(expr x) = 2 - (x-1)**2 enddef;
  path p, q;
  p := compute_curve(f, -1, 1.5, .1) scaled 1cm;
  q := compute_curve(g, -.5, 2, .1) scaled 1cm;
  fill buildcycle(p,reverse q) withcolor red+green;
  draw p withpen pencircle scaled 1bp;
  draw q withpen pencircle scaled 1bp;
  draw (-1cm,0) -- (2cm,0);
  draw (0,g(-.5)*1cm) -- (0,f(1.5)*1cm);
endfig;
end;
