input plain;
beginfig(28)
    pair A;
    A := (0,0);
    draw A withpen pencircle scaled 4bp;
    label.ulft(btex Upper left  etex, A);
    label.urt (btex Upper right etex, A);
    label.llft(btex Lower left  etex, A);
    label.lrt (btex Lower right etex, A);

endfig;
end;
