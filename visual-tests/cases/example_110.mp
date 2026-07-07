input plain;
beginfig(110)
  u:=1cm;
  path c[];
  c[1] := fullcircle scaled u;
  c[2] := c[1] shifted (0,.5u);
  draw c[1] dashed evenly;
  draw c[2] dashed evenly;
  draw buildcycle(c[1],c[2]) withpen pencircle scaled 1bp;
endfig;
end;
