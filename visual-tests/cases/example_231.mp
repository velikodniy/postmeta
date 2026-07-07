input plain;
beginfig(231)
  u:=1cm;
  path p;
  p =
  (0,u)
  for i=.1 step .1 until 10:
    hide( pair A; A = (i*u, (sind (i*180/3.14))/i *u);
          draw A withpen pencircle scaled 2pt )
    .. A
  endfor;
  draw p;
endfig;
end;
