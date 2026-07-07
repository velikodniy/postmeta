input plain;
beginfig(25)
  pair A, B, C, D;
  A:=(0,0); B:=(1cm,0);
  C:=(1cm,1cm); D:=(0,1cm);
  path p;
  p := A--C--B--D--cycle;
  fill p withcolor .8white;
  draw p;
endfig;
end;
