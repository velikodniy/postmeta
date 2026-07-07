input plain;
beginfig(61)
  u:=1cm;
  pair A, B, C, D;
  A = (0,0);
  D = (2u,0);
  B = (-u,2u);
  C = (3u,3u);

  draw A withpen pencircle scaled 4bp;
  draw B withpen pencircle scaled 4bp;
  draw C withpen pencircle scaled 4bp;
  draw D withpen pencircle scaled 4bp;
  draw A .. controls B and C .. D;

  pair a[];
  a[1] := A;
  a[2] := B;
  a[3] := C;
  a[4] := D;

  a[12]   := 1/2 [ a[1],   a[2]   ];
  a[23]   := 1/2 [ a[2],   a[3]   ];
  a[34]   := 1/2 [ a[3],   a[4]   ];
  a[123]  := 1/2 [ a[12],  a[23]  ];
  a[234]  := 1/2 [ a[23],  a[34]  ];
  a[1234] := 1/2 [ a[123], a[234] ];

  draw a[1234] withpen pencircle scaled 4bp;
endfig;
end;
