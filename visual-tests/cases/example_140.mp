input plain;
beginfig(140)
  for i=1 step -.01 until 0:
    fill fullcircle scaled (i*2cm) withcolor i*white;
  endfor;
  draw fullcircle scaled 2cm withpen pencircle scaled 2bp;
endfig;
end;
