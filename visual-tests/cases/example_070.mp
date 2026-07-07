input plain;
beginfig(70)
    pair A,B,C,D,M;
    A=(0,0); B=(2cm,3cm);
    C=(1cm,0); D=(-1cm,2cm);
    M = whatever [A,B];
    M = whatever [C,D];
    draw A--B;
    draw C--D;
    draw M withpen pencircle scaled 4bp;

endfig;
end;
