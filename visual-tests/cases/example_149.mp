input plain;
beginfig(149)
  def couleur(expr x) =
    if x>.5: (2*(1-x)) [red, blue];
    else:    (1-2x) [blue, red]
    fi
  enddef;
  for i=0 step .1 until 360:
    draw 2cm* (sind(2*i), cosd(3*i))
    withpen pencircle scaled 2bp
    withcolor couleur(i/360);
  endfor;
endfig;
end;
