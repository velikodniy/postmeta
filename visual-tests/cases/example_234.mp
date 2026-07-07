input plain;
vardef TEX primary s = s infont defaultfont scaled defaultscale enddef;
beginfig(234)
  numeric x;
  x = sind(60);
  draw TEX("$\sin 60 = " & decimal(x) & "$");

endfig;
end;
