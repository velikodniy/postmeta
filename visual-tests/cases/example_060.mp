input plain;
beginfig(60)
    u:=.5cm;
    pair A,B,C,D;
    A:=(0,0);   B:=(-u,2u);
    C:=(4u,3u); D:=(3u,0);
    draw A.. controls B and C .. D
         withpen pencircle scaled 2pt;
    draw B--C dashed evenly;
    drawarrow A--B;
    drawarrow D--C;

endfig;
end;
