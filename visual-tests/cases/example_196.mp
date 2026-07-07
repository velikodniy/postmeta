input plain;
beginfig(196)
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

  vardef trace_rectangles_left (suffix f)(expr a,b,inc) =
    save i; numeric i;
    for i=a step inc until b-inc:
      path p;
      p = (i,0)--(i+inc,0)--(i+inc,f(i))--(i,f(i))--cycle;
      p := p scaled 1cm;
      fill p withcolor .8*white;
      draw p;
    endfor;
  enddef;

  vardef f(expr x) = 2 ** x enddef;

  trace_rectangles_left(f,-2,2,.5);
  draw trace(f, -2,2,.1);
  axes;
endfig;
end;
