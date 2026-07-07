input plain;
beginfig(121)
  n:=7;
  draw for i=0 step 1 until n-1:
      1cm*up rotated (i*360/n) --
    endfor cycle;
endfig;
end;
