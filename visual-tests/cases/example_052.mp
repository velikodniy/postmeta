input plain;
beginfig(52)
  u:=1cm;
  path p;
  p := (u,0){up} ..
       (-u,0){down} --
       (-.2u,0){up} ..
       (.2u,0){down} --
       cycle;
  fill p withcolor .8*white;
  draw p withpen pencircle scaled 1bp;
endfig;
end;
