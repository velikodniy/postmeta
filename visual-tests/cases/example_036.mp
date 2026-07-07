input plain;
beginfig(36)
  pair A, B, C;
  A:=(0,0); B:=(1cm,0); C:=(0,1cm);
  draw A--B--C--cycle;
  fill fullcircle scaled 4bp shifted A withcolor white;
  fill fullcircle scaled 4bp shifted B withcolor white;
  fill fullcircle scaled 4bp shifted C withcolor white;
  draw fullcircle scaled 4bp shifted A;
  draw fullcircle scaled 4bp shifted B;
  draw fullcircle scaled 4bp shifted C;
endfig;
end;
