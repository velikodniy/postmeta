input plain;
beginfig(178)
% M est sur la bissectrice de l'angle A
vardef bissectrice(expr M,A,B,C) =
  (M-A) = whatever * (
    (A-C) rotated 1/2(angle(B-A) - angle(C-A)))
enddef;

% Le cercle inscrit
vardef cercle_inscrit(expr A,B,C) =
  save M, h; pair M, h;
  bissectrice(M,A,B,C);
  bissectrice(M,B,C,A);
  M-h = whatever * (B-C) rotated 90;
  h = whatever[B,C];
  fullcircle scaled 2 length(M-h) shifted M
enddef;

  pair A,B,C,M;
  u:=2cm;
  A=(0,0); B=(2u,-.5u); C=(u,u);
  draw A--B--C--cycle;
  bissectrice(M, A,B,C);
  bissectrice(M, B,C,A);
  draw M--A; draw M--B; draw M--C;
  draw cercle_inscrit(A,B,C);
endfig;
end;
