input plain;
beginfig(151)
  for i=0 step 1 until 360:
    pair P;
    P = 2cm* (sind(2*i), cosd(3*i));
    fill fullcircle scaled 4mm shifted P withcolor white;
    draw fullcircle scaled 4mm shifted P;
  endfor;
  picture p;
  p:=nullpicture;
  for i=-180 step 1 until 180:
    pair P;
    P = 2cm* (sind(2*i), cosd(3*i));
    addto p contour fullcircle scaled 4mm shifted P withcolor white;
    addto p doublepath fullcircle scaled 4mm shifted P
      withpen pencircle scaled .5bp;
  endfor;
  clip p to (.5cm,2.5cm) -- (.5cm,1.5cm)--
            (-.5cm,1.5cm) -- (-.5cm,2.5cm)--cycle;
  draw p;
endfig;
end;
