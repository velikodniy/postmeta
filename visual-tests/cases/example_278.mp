input plain;
input graph;
beginfig(278)
  picture gros_point;
  draw (0,0) withpen pencircle scaled 4bp;
  gros_point := currentpicture;
  currentpicture := nullpicture;
  draw begingraph(3cm,2cm)
    gdraw "data1" plot gros_point;
  endgraph;
endfig;
end;
