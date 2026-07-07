input plain;
beginfig(105)
    path p;
    p = (0,0){up} .. (2cm,0){down};
    draw p;
    draw point 0  of p withpen pencircle scaled 4bp;
    draw point .5 of p withpen pencircle scaled 4bp;
    draw point 1  of p withpen pencircle scaled 4bp;

endfig;
end;
