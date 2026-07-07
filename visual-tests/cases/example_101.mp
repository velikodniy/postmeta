input plain;
beginfig(101)
  pair A,B;
  A:=(1cm,2cm); B:=(2cm,1cm);
  numeric alpha;
  alpha = angle(A) - angle(B);
  drawarrow origin--A;
  drawarrow origin--B;
  drawarrow (origin--A) rotated -1/3 alpha;
  drawarrow (origin--A) rotated -2/3 alpha;
  drawarrow (origin--A) rotated -alpha;
endfig;
end;
