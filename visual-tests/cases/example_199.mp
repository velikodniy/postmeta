input plain;
beginfig(199)
  vardef trace (suffix f)(expr a,b,inc) =
    save i; numeric i;
    for i=a step inc until b:
      (i*1cm, f(i)*1cm) ..
    endfor (b*1cm, f(b)*1cm)
  enddef;

  vardef axes =
    save p; picture p;
    p:=nullpicture;
    addto p doublepath (-infinity,0)--(infinity,0) withpen currentpen;
    addto p doublepath (0,-infinity)--(0,infinity) withpen currentpen;
    clip p to bbox currentpicture;
    draw p;
  enddef;

  vardef maxf(suffix f)(expr a,b) =
    save m,i; numeric m,i;
    m:=f(a);
    for i=a step (b-a)/100 until b:
      if m<f(i): m:=f(i); fi;
    endfor;
    m
  enddef;

  vardef trace_rectangles_max (suffix f)(expr a,b,inc) =
    save i; numeric i;
    for i=a step inc until b-inc:
      path p; numeric m;
      m:=maxf(f,i,i+inc);
      p = (i,0)--(i+inc,0)--(i+inc,m)--(i,m)--cycle;
      p := p scaled 1cm;
      fill p withcolor .8*white;
      draw p;
    endfor;
  enddef;

  vardef f(expr x) = 4 - x**2 enddef;

  trace_rectangles_max(f,-2,2,.5);
  draw trace(f, -2,2,.1);
  axes;
endfig;
end;
