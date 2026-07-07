input plain;
beginfig(68)
  pair A,B,C,D;
  xpart A = ypart A = ypart B = xpart C = 0;
  xpart B = ypart C = xpart D = ypart D = 2cm;
  draw A--B--C--D--cycle withpen pencircle scaled 2bp;
endfig;
end;
