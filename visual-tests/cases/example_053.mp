input plain;
beginfig(53)
  u:=1cm;
  pair A,AA,B,BB,C,D;
  A  := ( .2u,  .05u);
  AA := ( .2u, -.05u);
  B  := (   u,  .05u);
  BB := (   u, -.05u);
  C  := (-.2u,     0);
  D  := (  -u,     0);
  path p;
  p:= B{up}    .. D{down} .. BB{up}  --
      AA{down} .. C{up}   .. A{down} -- cycle;
  fill p withcolor .8*white;
  draw p withpen pencircle scaled 1bp;
endfig;
end;
