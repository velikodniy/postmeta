input plain;
input graph;
beginfig(293)
    draw begingraph(3cm,2cm)
      gdraw "data1" withcolor red;
      glabel.lft(btex 1 etex, 8);
      gdraw "data2" withcolor blue;
      glabel.bot(btex 2 etex, 9);
    endgraph;

endfig;
end;
