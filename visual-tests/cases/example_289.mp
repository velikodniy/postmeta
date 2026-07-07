input plain;
input graph;
beginfig(289)
  draw begingraph(3cm,2cm)
    gdata("data1", v,

            % Le dessus
            path p;
            augment p (v1,v2);
            augment p (v1 Sadd "1",v2);
            augment p (v1 Sadd "1.5", v2 Sadd "10");
            augment p (v1 Sadd ".5",  v2 Sadd "10");
            gfill p--cycle withcolor white;
            gdraw p--cycle;

            % Le c�t�
            path p;
            augment p (v1 Sadd "1",0);
            augment p (v1 Sadd "1",v2);
            augment p (v1 Sadd "1.5", v2 Sadd "10");
            augment p (v1 Sadd "1.5", "10");
            gfill p--cycle withcolor .5white;
            gdraw p--cycle;

            % Le devant
            path p;
            augment p (v1,0);
            augment p (v1,v2);
            augment p (v1 Sadd "1",v2);
            augment p (v1 Sadd "1",0);
            gfill p--cycle withcolor .8white;
            gdraw p--cycle;

           );
 endgraph;
endfig;
end;
