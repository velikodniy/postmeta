input plain;
vardef TEX primary s = s infont defaultfont scaled defaultscale enddef;
beginfig(235)
picture _TEX_pic;

def largeur(expr p) =
  if picture p:
    xpart( lrcorner(p) - llcorner(p) )
  elseif string p:
    hide(_TEX_pic := TEX(p);)
    xpart( lrcorner(_TEX_pic) - llcorner(_TEX_pic) )
  else:
    hide( errmessage("largeur: wrong type"); 0)
  fi
enddef;

def hauteur(expr p) =
  if picture p:
    ypart(ulcorner(p))
  elseif string p:
    hide(_TEX_pic := TEX(p);)
    ypart(ulcorner(_TEX_pic))
  else:
    hide( errmessage("hauteur: wrong type"); 0)
  fi
enddef;

def profondeur (expr p) =
  if picture p:
    -ypart(llcorner(p))
  elseif string p:
    hide(_TEX_pic := TEX(p);)
    -ypart(llcorner(_TEX_pic))
  else:
    hide( errmessage("profondeur: wrong type"); 0)
  fi
enddef;

  picture p;
  string s;
  s := "\huge\LaTeX";
  p := TEX(s);
  drawarrow (0,0) -- (largeur(s),0) withcolor red;
  drawarrow (0,0) -- (0,hauteur(s)) withcolor green;
  drawarrow (0,0) -- (0,-profondeur(s)) withcolor blue;
  draw p;
  draw bbox p;
endfig;
end;
