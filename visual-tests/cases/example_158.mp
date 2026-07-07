input plain;
beginfig(158)
  path p;
  p := (0,0){up} .. (1cm,1cm) .. (1cm,0);
  draw p;
  draw point 1/2length(p) of p
    withpen pencircle scaled 4bp withcolor red;
  draw point (arctime (1/2 arclength(p)) of p) of p
    withpen pencircle scaled 4bp;

endfig;
end;
