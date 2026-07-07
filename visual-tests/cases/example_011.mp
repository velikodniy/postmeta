input plain;
beginfig(11)
    pair A, B, C;
    A:=(0,0); B:=(1cm,0); C:=(0,1cm);
    draw A--B;
    draw B--C dashed evenly;
    draw C--A dashed withdots;

endfig;
end;
