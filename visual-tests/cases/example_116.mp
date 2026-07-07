input plain;
beginfig(116)
  u:=2cm;
  pair A[], B[], C[], D[], E[];
  path p[];

  A[0] = u*up;
  for i=1 upto 10:
    A[i] := A[i-1] rotated 72;
  endfor;
  for i=0 upto 4:
    p[i] := A[i]--A[i+1];
    draw p[i];
    draw (point 1 of p[i]) --
    ( (point 1 of p[i]) + 4mm*unitvector(direction 1 of p[i]));
    draw (point 0 of p[i]) --
    ( (point 0 of p[i]) - 4mm*unitvector(direction 0 of p[i]));
  endfor

  for i=0 upto 9:
    B[i] := 1/2[ A[i], A[i+1] ];
  endfor;
  B[5]:=B[0];

  for i=0 upto 9:
    C[i] := .8*B[i];
  endfor;

  for i=0 upto 4:
    p[i] := B[i] --- C[i] .. C[i+2]{dir 72i};
    draw p[i];
    draw (point 2 of p[i]) --
    ( (point 2 of p[i]) + 4mm*unitvector(direction 2 of p[i]));
    draw (point 0 of p[i]) --
    ( (point 0 of p[i]) - 4mm*unitvector(direction 0 of p[i]));
  endfor;
  for i=0 upto 4:
    draw subpath(1,1.4) of p[i] withpen pencircle scaled 4bp withcolor white;
    draw subpath(0,1.5) of p[i];
  endfor;

  for i=0 upto 4:
    draw A[i] withpen pencircle scaled 4bp;
    draw B[i] withpen pencircle scaled 4bp;
    draw C[i] withpen pencircle scaled 4bp;
  endfor;
endfig;
end;
