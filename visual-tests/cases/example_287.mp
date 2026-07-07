input plain;
input graph;
beginfig(287)
  draw begingraph(3cm,2cm)
    gdata("data1", v,
          path p;
          augment p (v1,0);
          augment p (v1,v2);
          augment p (v1 Sadd "1",v2);
          augment p (v1 Sadd "1",0);
          gdraw p--cycle;
         );
  endgraph;
endfig;
end;
