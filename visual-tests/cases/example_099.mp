input plain;
beginfig(99)
    pair A, B;
    A := (0,0); B := (2cm,1cm);
    draw A withpen pencircle scaled 4bp;
    draw B withpen pencircle scaled 4bp;
    draw fullcircle scaled abs(B-A) shifted 1/2[A,B];

endfig;
end;
