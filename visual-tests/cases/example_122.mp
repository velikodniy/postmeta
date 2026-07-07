input plain;
beginfig(122)
  path p;
  p = (0,0) .. (-1cm,2cm) .. (2cm,1cm) .. (1cm,0);
  draw p;
  n:=10;
  for i=0 step 1 until n:
    draw point (i/n*length(p)) of p
         withpen pencircle scaled 4bp;
  endfor;
endfig;
end;
