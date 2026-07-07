input plain;
beginfig(120)
  n:=5;
  draw for i=0 step 1 until n-1:
      1cm*up rotated (i*360/n) --
    endfor cycle;
endfig;
end;
