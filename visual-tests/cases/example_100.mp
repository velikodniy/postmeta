input plain;
beginfig(100)
    pair A;
    A:=(2cm,2cm);
    drawarrow origin--A;
    drawarrow (origin--A) rotated -1/3 angle(A);
    drawarrow (origin--A) rotated -2/3 angle(A);
    drawarrow (origin--A) rotated -angle(A);

endfig;
end;
