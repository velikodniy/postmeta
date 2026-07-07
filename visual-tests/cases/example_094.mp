input plain;
beginfig(94)
  u:=3mm;
  picture mickey;
  fill fullcircle scaled 2u withcolor .8white;
  fill fullcircle scaled u shifted (u*dir30)
       withcolor .8white;
  fill fullcircle scaled u shifted (u*dir150)
       withcolor .8white;
  mickey := currentpicture;
  currentpicture := nullpicture;

  transform T;
  (0,0) transformed T = (0,0);
  (1,0) transformed T = (1,1);
  (0,1) transformed T = (1,0);

  draw mickey transformed T;
endfig;
end;
