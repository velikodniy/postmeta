input plain;
beginfig(147)
  draw for i=0 step 10 until 360:
    2cm* (sind(2*i), cosd(3*i)) ..
  endfor cycle;
endfig;
end;
