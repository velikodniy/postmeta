input plain;
beginfig(233)
  path p;
  p := (0,0) -- (1cm,0);
  show ahangle;
  begingroup
    interim ahangle := 30;
    interim linejoin := mitered;
    interim linecap := butt;
    drawarrow p withpen pencircle scaled 2bp;
  endgroup;
  begingroup
    interim ahangle := 60;
    drawarrow p shifted (0,-5mm) withpen pencircle scaled 2bp;
  endgroup;

endfig;
end;
