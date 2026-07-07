input plain;
beginfig(27)
    pair A;
    A := (0,0);
    draw A withpen pencircle scaled 4bp;
    label.top(btex Above etex, A);
    label.bot(btex Below etex, A);
    label.rt (btex Right etex, A);
    label.lft(btex Left  etex, A);

endfig;
end;
