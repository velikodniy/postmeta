input plain;
beginfig(113)
    path p, q;
    p = (0,0){up} .. (2cm,0){up};
    q = (0,1cm){dir -60}..(1cm,-1cm)..{dir 60}(2cm,1cm);
    draw p; draw q;
    draw p intersectionpoint q withpen pencircle scaled 4bp;

endfig;
end;
