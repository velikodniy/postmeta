input plain;
beginfig(9)
    pair A, B, C;
    A:=(0,0); B:=(1cm,0); C:=(0,1cm);
    draw A--B--C--cycle;
    draw A--B withpen pencircle scaled 2bp;

endfig;
end;
