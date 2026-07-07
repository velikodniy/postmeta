input plain;
beginfig(54)
  u:=1cm;
  pair A,B,C,D;
  A:=(0,0);
  B:=u*dir 60;
  C:=u*dir -60;
  D:=(2u,0);
  draw A withpen pencircle scaled 4bp;
  draw B withpen pencircle scaled 4bp;
  draw C withpen pencircle scaled 4bp;
  draw D withpen pencircle scaled 4bp;
  draw A--D--B--D--C;
  draw A{up}..B;
  draw A{down}..C;
  draw A{dir 30}..B;
  draw A{dir -30}..C;
endfig;
end;
