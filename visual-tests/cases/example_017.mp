input plain;
beginfig(17)
    pair A, B, C;
    A:=(0,0); B:=(1cm,0); C:=(0,1cm);
    drawarrow C--B--A;
    drawarrow A--C withpen pencircle scaled 2bp;

endfig;
end;
