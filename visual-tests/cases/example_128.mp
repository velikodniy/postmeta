input plain;
beginfig(128)
  u := 5mm;
  % vardef est n�cessaire pour pouvoir passer f en argument
  vardef f(expr x) = x**2 -.1 enddef;
  def axes(expr xmin,xmax,ymin,ymax) =
    draw ( (xmin,0) -- (xmax,0) ) scaled u;
    draw ( (0,ymin) -- (0,ymax) ) scaled u;
  enddef;
  def courbe(suffix f)(expr xmin, xmax, M) =
    draw ( ( xmin, f(xmin) )
    for i=1 upto M:
    -- ( xmin + (i/M)*(xmax - xmin), f( xmin + (i/M)*(xmax - xmin) ))
    endfor ) scaled u;
  enddef;
  vardef newton(suffix f)(expr y, h, M) =
    save x,t;
    numeric x,t; x:=y;
    for i=1 upto M:
      t := x - f(x)/(  (f(x+h) - f(x))/h );
      draw ( (x,f(x)) -- (t,0) -- (t,f(t)) ) scaled u;
      x := t;
    endfor;
  enddef;
  axes(-.5,2,-.5,4);
  courbe(f,-.5,2, 100);
  newton(f, 2, .01, 10);
endfig;
end;
