input plain;
input graph;
beginfig(290)
  draw begingraph(3cm,2cm)
    path p,q;
    gdata("data1", v,
          augment.p(v1,v2);
         );
    q:= (xpart point 0 of p, 0) -- p --
      (xpart point length(p) of p, 0) -- cycle;
    gfill q withcolor .8white;
    gdraw p withpen pencircle scaled 2bp;
  endgraph;
endfig;
end;
