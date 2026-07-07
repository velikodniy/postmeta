input plain;
beginfig(302)
   path p;
   p := subpath(1,3) of fullcircle scaled 2cm;
   interim linejoin := mitered;
   interim linecap := butt;
   interim ahangle := 30;

   interim ahlength := 2bp;
   drawarrow p withpen pencircle scaled 2bp;

   interim ahlength := 4bp;
   drawarrow p shifted (0,-5mm) withpen pencircle scaled 2bp;

   interim ahlength := 6bp;
   drawarrow p shifted (0,-10mm) withpen pencircle scaled 2bp;

endfig;
end;
