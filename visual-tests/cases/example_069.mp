input plain;
beginfig(69)
    pair A,B,C,D,M;
    numeric lambda, mu;
    A=(0,0); B=(2cm,3cm);
    C=(1cm,0); D=(-1cm,2cm);
    M = lambda [A,B];
    M = mu     [C,D];
    draw A--B;
    draw C--D;
    draw M withpen pencircle scaled 4bp;

endfig;
end;
