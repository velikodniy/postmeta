input plain;
beginfig(93)
  u:=3mm;
  picture mickey;
  mickey := nullpicture;
  addto mickey contour fullcircle scaled 2u
        withcolor .8white;
  addto mickey contour fullcircle scaled u
        shifted (u*dir30) withcolor .8white;
  addto mickey contour fullcircle scaled u
        shifted (u*dir150) withcolor .8white;

  transform T;
  (0,0) transformed T = (0,0);
  (1,0) transformed T = (1,1);
  (0,1) transformed T = (1,0);

  draw mickey transformed T;
endfig;
end;
