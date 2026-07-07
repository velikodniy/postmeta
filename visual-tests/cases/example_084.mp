input plain;
beginfig(84)
    pair A,B,C,D;
    u:=2cm;
    A=(0,0); B=(u,0); C=(u,u); D=(0,u);

    transform T;
    A transformed T = 1/5[A,B];
    B transformed T = 1/5[B,C];
    C transformed T = 1/5[C,D];

    path p;
    p = A--B--C--D--cycle;
    draw p;
    draw p transformed T;

endfig;
end;
