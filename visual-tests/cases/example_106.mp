input plain;
beginfig(106)
    path p;
    p = (0,0){up} .. (2cm,0){down};
    draw p;
    pair A;
    A := point 0  of p;
    B := A + 1cm*unitvector(direction 0  of p);
    drawarrow A--B withpen pencircle scaled 1bp;
    A := point .5 of p;
    B := A + 1cm*unitvector(direction .5 of p);
    drawarrow A--B withpen pencircle scaled 1bp;
    A := point 1  of p;
    B := A + 1cm*unitvector(direction 1  of p);
    drawarrow A--B withpen pencircle scaled 1bp;

endfig;
end;
