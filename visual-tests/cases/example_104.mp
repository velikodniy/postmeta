input plain;
beginfig(104)
  pair A,B,C,M,h;
  u:=2cm;
  A=(0,0); B=(2u,-.5u); C=(u,u);
  draw A--B--C--cycle;
  (M-A) = whatever * (
    (A-C) rotated 1/2( angle(B-A) - angle(C-A)) );
  (M-B) = whatever * (
    (B-A) rotated 1/2( angle(C-B) - angle(A-B)) );
  draw M--A; draw M--B; draw M--C;
  M-h = whatever * (B-C) rotated 90;
  h = whatever[B,C];
  draw fullcircle scaled 2 abs(M-h) shifted M;
endfig;
end;
