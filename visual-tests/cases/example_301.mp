input plain;
beginfig(301)
   path p;
   p := subpath(1,3) of fullcircle scaled 2cm;
   interim linejoin := mitered;
   interim linecap := butt;

   interim ahangle := 30;
   drawarrow p withpen pencircle scaled 2bp;

   interim ahangle := 45;
   drawarrow p shifted (0,-5mm) withpen pencircle scaled 2bp;

   interim ahangle := 60;
   drawarrow p shifted (0,-10mm) withpen pencircle scaled 2bp;

endfig;
end;
