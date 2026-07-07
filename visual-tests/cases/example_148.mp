input plain;
beginfig(148)
  for i=0 step .1 until 360:
    col := i/360;
    draw 2cm* (sind(2*i), cosd(3*i))
    withpen pencircle scaled 2bp
    withcolor
      if col>.5: (2*(1-col)) [red, blue]
      else:    (1-2col) [blue, red]
      fi;
  endfor;
endfig;
end;
