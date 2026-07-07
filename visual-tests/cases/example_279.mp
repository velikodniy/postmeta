input plain;
input graph;
beginfig(279)
  picture gros_point;
  gros_point := nullpicture;
  addto gros_point doublepath (0,0)
        withpen pencircle scaled 4bp;
  draw begingraph(3cm,2cm)
    gdraw "data1" plot gros_point;
  endgraph;
endfig;
end;
