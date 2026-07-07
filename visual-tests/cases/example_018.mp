input plain;
beginfig(18)
    pair A, B, C;
    A:=(0,0); B:=(1cm,0); C:=(0,1cm);
    draw C--B--A--cycle;
    drawdblarrow A--C withpen pencircle scaled 2bp;

endfig;
end;
