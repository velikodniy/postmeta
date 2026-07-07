input plain;
beginfig(91)
    picture pic;
    pic := nullpicture;
    addto pic contour fullcircle scaled 1cm
      withcolor .8white;
    addto pic doublepath fullcircle scaled 1cm
      withpen pencircle scaled .5bp;
    addto pic also pic shifted (1mm,1mm);
    draw pic;

endfig;
end;
