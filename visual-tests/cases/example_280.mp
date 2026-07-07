input plain;
input graph;
beginfig(280)
  picture croix;
  croix := nullpicture;
  addto croix doublepath (-2bp,2bp)--(2bp,-2bp)
              withpen pencircle scaled 1bp;
  addto croix doublepath (-2bp,-2bp)--(2bp,2bp)
              withpen pencircle scaled 1bp;
  picture gros_carre;
  gros_carre := nullpicture;
  addto gros_carre contour unitsquare shifted (-.5,-.5) scaled 2bp;

  draw begingraph(3cm,2cm)
    gdraw "data1";
    gdraw "data1" plot croix;
    gdraw "data2";
    gdraw "data2" plot gros_carre;
  endgraph;
endfig;
end;
