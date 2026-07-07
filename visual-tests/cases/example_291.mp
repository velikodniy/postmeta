input plain;
input graph;
beginfig(291)
  draw begingraph(3cm,2cm)
    gdata("data1",
      v,
      path p;
      augment p ("0", i);
      augment p (v2, i);
      augment p (v2, i Sadd ".5");
      augment p (0, i Sadd ".5");
      gfill p--cycle withcolor .8white;
      gdraw p--cycle;
      );
    autogrid(otick.bot,);
  endgraph;
endfig;
end;
