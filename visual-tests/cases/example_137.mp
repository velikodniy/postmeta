input plain;
beginfig(137)
  path p; u:=1cm;
  p = fullcircle xscaled -u yscaled 3u;
  draw p;
  for i=2 step .5 until 6:
    draw (point 2 of p){down} .. (point i of p);
  endfor;
endfig;
end;
