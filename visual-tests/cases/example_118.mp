input plain;
beginfig(118)
    for i=0 step 1 until 3:
      draw 1cm*right rotated (i*90)
           withpen pencircle scaled 4bp;
    endfor;

endfig;
end;
