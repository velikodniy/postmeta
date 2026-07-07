input plain;
beginfig(89)
  u:=3mm;
  transform T;
  xpart T = ypart T = 0;
  xxpart T = 1;
  yxpart T = 2;
  xypart T = 3;
  yypart T = 4;

  fill fullcircle scaled 2u transformed T withcolor .8white;
  fill fullcircle scaled u shifted (u*dir30) transformed T
       withcolor .8white;
  fill fullcircle scaled u shifted (u*dir150) transformed T
       withcolor .8white;
endfig;
end;
