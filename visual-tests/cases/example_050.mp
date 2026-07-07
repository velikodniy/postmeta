input plain;
beginfig(50)
      def draw_angle(expr A, O, B, n) =
    draw_angle_(A,O,B,5mm);
    if n>1 : draw_angle_(A,O,B,4.5mm); fi;
    if n>2 : draw_angle_(A,O,B,4mm);   fi;
    if n>3 : draw_angle_(A,O,B,5.5mm); fi;
  enddef;
  def draw_angle_(expr A,O,B,d) =
    draw (O + d*unitvector(A-O))
         { d*unitvector(A-O) rotated 90 }
         ..
         { d*unitvector(B-O) rotated 90 }
         (O + d*unitvector(B-O));
  enddef;
  pair A, B, C;
  A := (0,0);
  B := (3cm,0);
  C := (1cm,2cm);
  draw A--B--C--cycle;
  draw_angle(B,A,C,1);
  draw_angle(C,B,A,2);
  draw_angle(A,C,B,3);
endfig;
end;
