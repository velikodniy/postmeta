input plain;
beginfig(108)
  u:=1cm;
  path p,q;
  p := (0,0){up} .. (u,2u){up};
  q := (u,0){up} .. (0,2u){up};
  draw p;
  draw subpath(0,.4) of q withpen pencircle scaled 1bp;
  draw subpath(.6,1) of q withpen pencircle scaled 1bp;
endfig;
end;
