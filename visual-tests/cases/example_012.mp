input plain;
beginfig(12)
    pair A, B, C;
    A:=(0,0); B:=(1cm,0); C:=(0,1cm);
    draw A--B withpen pencircle scaled 2bp withcolor .8white;
    draw B--C withpen pencircle scaled 2bp withcolor .6white;
    draw C--A withpen pencircle scaled 2bp withcolor .4white;

endfig;
end;
