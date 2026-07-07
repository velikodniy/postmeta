input plain;
beginfig(141)
  u:=5mm;
  path p;
  p = (0,0) .. (-1,1) .. (2,0) .. (0,-3) .. cycle;
  p := p shifted (-1,0);
  for i=1 step -.01 until 0:
    fill p scaled (i*u) withcolor i*white;
  endfor;
  draw p scaled u withpen pencircle scaled 2bp;
endfig;
end;
