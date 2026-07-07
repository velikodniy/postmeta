input plain;
beginfig(80)
  u:=1cm;
  path p;     p := (0,0) -- (u,0);
  pair A;     A := (u,-u);
  numeric a;  a := 90;
  drawarrow p withpen pencircle scaled 1bp;
  draw A withpen pencircle scaled 4bp;
  label ulft ( btex $A$ etex, A );
  draw (0,0) withpen pencircle scaled 4bp;
  label bot ( btex $O$ etex, (0,0) );
  for i=0 upto 10:
    drawarrow p shifted -(i*A/10) withcolor red;
  endfor;
  for i=0 upto 10:
    drawarrow p shifted -A rotated (i*a/10) withcolor green;
  endfor;
  for i=0 upto 10:
    drawarrow p shifted -A rotated a shifted (i*A/10) withcolor blue;
  endfor;
endfig;
end;
