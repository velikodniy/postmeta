input plain;
beginfig(212)
  numeric n;
  n:=10;
  path p;
  p := for i=0 upto n-1:
    ((1cm + 3mm*normaldeviate,0) rotated (i*360/n)) ..
  endfor cycle;
  fill p withcolor .8white;
  draw p;
endfig;
end;
