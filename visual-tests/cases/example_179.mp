input plain;
beginfig(179)
vardef premiere_trisectrice (expr M, A,B,C) =
  (M-A) = whatever * ( (A-B) rotated 1/3 (angle(C-A) - angle(B-A)) )
enddef;

vardef deuxieme_trisectrice (expr M, A,B,C) =
  (M-A) = whatever * ( (A-B) rotated 2/3 (angle(C-A) - angle(B-A)) )
enddef;

  pair A,B,C,M[];
  u:=2cm;
  A=(0,0); B=(2u,-.5u); C=(u,u);
  draw A--B--C--cycle;

  premiere_trisectrice(M1,A,B,C);
  deuxieme_trisectrice(M1,B,C,A);
  premiere_trisectrice(M2,B,C,A);
  deuxieme_trisectrice(M2,C,A,B);
  premiere_trisectrice(M3,C,A,B);
  deuxieme_trisectrice(M3,A,B,C);

  draw M1--A; draw M1--B;
  draw M2--B; draw M2--C;
  draw M3--C; draw M3--A;

  draw M1--M2--M3--cycle;
endfig;
end;
