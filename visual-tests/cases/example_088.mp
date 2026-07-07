input plain;
beginfig(88)
  u:=3mm;
  transform T;
  (0,0) transformed T = (0,0);
  (1,0) transformed T = (1,1);
  (0,1) transformed T = (1,0);

  fill fullcircle scaled 2u transformed T withcolor .8white;
  fill fullcircle scaled u shifted (u*dir30) transformed T
       withcolor .8white;
  fill fullcircle scaled u shifted (u*dir150) transformed T
       withcolor .8white;
endfig;
end;
