input plain;
beginfig(225)
  path p;
  p := (0,0) -- (2cm,0);
  def doit (suffix p)(expr t) =
    begingroup
      interim linecap := t;
      draw p withpen pencircle scaled 5mm withcolor .8white;
    endgroup;
    draw point 0 of p withpen pencircle scaled 4bp;
    draw point 1 of p withpen pencircle scaled 4bp;
    p := p shifted (0,-7mm)
  enddef;
  doit(p,rounded);
  doit(p,butt);
  doit(p,squared);

endfig;
end;
