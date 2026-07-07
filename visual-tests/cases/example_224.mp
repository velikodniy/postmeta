input plain;
beginfig(224)
      u := 5mm;
  draw (-2u,0) -- (2u,0);
  draw (0,-u) -- (0,4u);
  draw (-2u,4u) for i=-1.9 step .1 until 2.01: .. (i*u, i*i*u) endfor
    withpen pencircle scaled 1bp;
  draw bbox currentpicture withpen pensquare scaled 2bp withcolor .8white;
  draw bbox currentpicture withpen pensquare scaled 2bp withcolor .8white;
endfig;
end;
