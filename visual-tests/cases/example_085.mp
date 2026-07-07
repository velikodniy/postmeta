input plain;
beginfig(85)
    pair A,B,C,D;
    u:=2cm;
    A=(0,0); B=(u,0); C=(u,u); D=(0,u);

    transform T;
    A transformed T = 1/5[A,B];
    B transformed T = 1/5[B,C];
    C transformed T = 1/5[C,D];

    path p;
    p = A--B--C--D--cycle;
    for i=0 upto 100:
      draw p;
      p:= p transformed T;
    endfor;

endfig;
end;
