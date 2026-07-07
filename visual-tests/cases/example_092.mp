input plain;
beginfig(92)
  u:=3mm;
  picture mickey;
  mickey := nullpicture;
  addto mickey contour fullcircle scaled 2u
        withcolor .8white;
  addto mickey contour fullcircle scaled u
        shifted (u*dir30) withcolor .8white;
  addto mickey contour fullcircle scaled u
        shifted (u*dir150)
        withcolor .8white;
  draw mickey;
endfig;
end;
