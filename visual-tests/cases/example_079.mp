input plain;
beginfig(79)
  u:=1cm;
  path p;     p := (0,0) -- (u,0);
  pair A;     A := (u,-u);
  numeric a;  a := 90;
  drawarrow p withpen pencircle scaled 1bp;
  drawarrow p rotatedaround( A, a );
  drawarrow p shifted -A rotated a shifted A
    withpen pencircle scaled 1bp dashed withdots;
endfig;
end;
