input plain;
input boxes;
beginfig(259)
vardef boxit@#(text tt) =
  beginbox_("boxpath_","sizebox_",@#,tt);
  generic_declare(pair) _n.sw, _n.s, _n.se, _n.e, _n.ne, _n.n, _n.nw, _n.w;
  0 = xpart (@#nw-@#sw) = ypart(@#se-@#sw);
  0 = xpart(@#ne-@#se) = ypart(@#ne-@#nw);
  @#s = .5[@#sw,@#se];
  @#n = .5[@#ne,@#nw];
  xpart @#w = xpart @#nw;
  xpart @#e = xpart @#ne;
  ypart @#w = ypart @#c = ypart @#e;
  @#ne-@#c = (@#dx,@#dyup) +
             (xpart(.5*(urcorner pic_@# - llcorner pic_@#)), ypart urcorner pic_@#);
  @#c-@#sw = (@#dx,@#dydown) +
             (xpart(.5*(urcorner pic_@# - llcorner pic_@#)), -ypart lrcorner pic_@#);
  endbox_(clearb_,@#);
enddef;

def sizebox_(suffix $) =
  if unknown $.dx: $.dx=defaultdx; fi
  if unknown $.dyup:
    if unknown $.dy:
      $.dyup=defaultdy
    else:
      $.dyup=$.dy
    fi;
  fi;
  if unknown $.dydown:
    if unknown $.dy:
      $.dydown=defaultdy
    else:
      $.dydown=$.dy
    fi;
  fi;
enddef;

vardef clearb_(suffix $) =
  _n_ := str $;
  generic_redeclare(numeric) _n.sw, _n.s, _n.se, _n.e, _n.ne, _n.n, _n.nw, _n.w,
    _n.c, _n.off, _n.dx, _n.dy, _n.dyup, _n.dy_down;
enddef;

  draw (0,0) -- (5cm,0) withcolor red;
  boxjoin(b.c - a.c = (1cm,0); ypart( b.ne - a.ne ) = 0; ypart( b.se - a.se ) = 0;);
  boxit a (btex a etex);
  boxit b (btex b etex);
  boxit c (btex c etex);
  boxit d (btex d etex);
  boxit e (btex e etex);
  drawboxed(a,b,c,d,e);
endfig;
end;
