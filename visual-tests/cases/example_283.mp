input plain;
input graph;
beginfig(283)
  interim linecap := squared;
  interim linejoin := mitered;
  draw begingraph(3cm,2cm)
    path p;
    gdata("data1",
      v,
      augment.p(v1,v2);
      );
    gdraw p withpen pencircle scaled 2bp;
    gdraw p withpen pencircle scaled 1bp withcolor .8white;
  endgraph;
endfig;
end;
