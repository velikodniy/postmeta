input plain;
input graph;
beginfig(286)
  interim linecap:=2;
  draw begingraph(3cm,2cm)
    gdata("data1",
          v,
          path p;
          augment p (v1,0);
          augment p (v1,v2);
          gdraw p withpen pencircle scaled 4bp;
         );
  endgraph;
endfig;
end;
