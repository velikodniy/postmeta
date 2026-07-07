input plain;
beginfig(230)
  draw fullcircle shifted (.5,.5) xscaled 18.2cm yscaled 4cm;
  special(
    "gsave " &
    "/Times-Roman findfont 150 scalefont setfont " &
    "0 0 moveto (ABCabc) false charpath clip stroke " &
    "gsave 300 0 translate " &
    "  2 4 600 {dup 0 moveto 0 exch 0 exch 0 360 arc stroke} for " &
    "grestore " &
    "grestore "
    );

endfig;
end;
