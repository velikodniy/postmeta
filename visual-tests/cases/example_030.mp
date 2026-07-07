input plain;
beginfig(30)
  pair A, B, C;
  A:=(0,0); B:=(1cm,0); C:=(0,1cm);
  draw A--B--C--cycle;
  dotlabel.llft(btex $A$ etex, A);
  dotlabel.lrt(btex $B$ etex, B);
  dotlabel.top(btex $C$ etex, C);
endfig;
end;
