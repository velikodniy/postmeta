input plain;
input boxes;
beginfig(269)
def begindiag =
  begingroup;
  save _diag_x, _diag_x_max, _diag_y, _diag_y_max, _diag;
  numeric _diag_x, _diag_x_max, _diag_y, _diag_y_max;
  string _diag[][];
  % Num�ro de ligne et de colonne courrants
  _diag_x = -1; _diag_y = 0;
  % Num�ro de ligne et de colonne maximaux
  _diag_x_max = _diag_y_max = 0;
  save _diag_ar_n, _diag_ar_source, _diag_ar_but, _diag_ar_up, _diag_ar_down;
  % Nombre de fl�ches
  numeric _diag_ar_n; _diag_ar_n=-1;
  % Source et but de la fl�che
  pair _diag_ar_source[], _diag_ar_but[];
  % Ce qu'il faut �crire au dessus ou au dessous
  string _diag_ar_up[], _diag_ar_down[];
  save _diag_ar_curved, _diag_ar_shape, _diag_ar_color, _diag_ar_width;
  % � courbure � (c'est une distance)
  numeric _diag_ar_curved[];
  % Forme de la fl�che
  string _diag_ar_shape[];
  % Couleur, �paisseur, pointill�s
  color _diag_ar_color[];
  numeric _diag_ar_width[];
  picture _diag_ar_dashed[];
enddef;

def node expr A =
  _diag_x := _diag_x + 1;
  _diag_x_max := max(_diag_x,_diag_x_max);
  _diag[_diag_x][_diag_y] := A;
enddef;

def nextline =
  _diag_x := -1;
  _diag_y := _diag_y + 1;
  _diag_y_max := max(_diag_y, _diag_y_max);
enddef;

tertiarydef a => b = a, b enddef;
def even (expr a) = not odd(a) enddef;

vardef rarrowto(expr a,b)(text t) =
  save i,p;
  _diag_ar_n := _diag_ar_n + 1;
  _diag_ar_source[_diag_ar_n] = (_diag_x, _diag_y);
  _diag_ar_but[_diag_ar_n] = (_diag_x + a, _diag_y + b);

  numeric i; i:=0;
  string current;
  for p=t:
    if even(i):
      current := p;
    else:
      if current = "above":
        _diag_ar_up[_diag_ar_n] = p;
      elseif current = "below":
        _diag_ar_down[_diag_ar_n] = p;
      elseif current = "shape":
        _diag_ar_shape[_diag_ar_n] = p;
      elseif current = "curved":
        _diag_ar_curved[_diag_ar_n] = p;
      elseif current = "color":
        _diag_ar_color[_diag_ar_n] = p;
      elseif current = "width":
        _diag_ar_width[_diag_ar_n] = p;
      elseif current = "dashed":
        _diag_ar_dashed[_diag_ar_n] = p;
      else:
        errmessage("rarrowto: Wrong argument "&ditto&current&ditto);
      fi;
    fi;
    i := i + 1;
  endfor;
  if odd i:
    errmessage("rarrowto: Odd number of arguments "&decimal(i));
  fi;
enddef;

%% Les t�tes de fl�ches

picture withsmalldots, notdashed;
withsmalldots := withdots scaled .3;
notdashed := dashpattern(on 50cm);

vardef diag_arrow_head (expr p, t) =
  save A,B,C,u; pair A,B,C,u;
  B := point t of p;
  u := -unitvector(direction t of p);
  A := B + ahlength*u rotated(-ahangle);
  C := B + ahlength*u rotated(+ahangle);
  A .. {-u} B {u} .. C
enddef;

vardef diag_arrow_bar (expr p, t) =
  save A,B,C,u; pair A,B,C,u;
  B := point t of p;
  u := unitvector(direction t of p);
  A := B + ahlength*sind(ahangle)*u rotated(90);
  C := B + ahlength*sind(ahangle)*u rotated(-90);
  A .. B .. C
enddef;

%% Les fl�ches

def diag_draw_arrow_default(suffix a,b)(expr curved, w, col, dash) =
  p = a.c ..
  (1/2 [a.c,b.c] + curved*unitvector(b.c-a.c) rotated 90)
  .. b.c;
  pp := p cutbefore bpath.a cutafter bpath.b;
  draw pp
    withcolor col withpen pencircle scaled w dashed dash;
  draw diag_arrow_head (pp, length(pp))
    withcolor col withpen pencircle scaled w;
enddef;

def diag_draw_arrow_middle(suffix a,b)(expr curved, w, col, dash) =
  p = a.c ..
  (1/2 [a.c,b.c] + curved*unitvector(b.c-a.c) rotated 90)
  .. b.c;
  pp := p cutbefore bpath.a cutafter bpath.b;
  draw pp
    withcolor col withpen pencircle scaled w dashed dash;
  draw diag_arrow_head(p,1)
    withcolor col withpen pencircle scaled w;
enddef;

def diag_draw_arrow_epi(suffix a,b)(expr curved, w, col, dash) =
  p = a.c ..
  (1/2 [a.c,b.c] + curved*unitvector(b.c-a.c) rotated 90)
  .. b.c;
  pp := p cutbefore bpath.a cutafter bpath.b;
  draw pp
    withcolor col withpen pencircle scaled w dashed dash;
  draw diag_arrow_head (pp, length(pp))
    withcolor col withpen pencircle scaled w;
  path ppp;
  ppp := pp cutafter (fullcircle scaled 1mm shifted point length(pp) of pp);
  draw diag_arrow_head(ppp, length(ppp))
    withcolor col withpen pencircle scaled w;
enddef;

def diag_draw_arrow_mono(suffix a,b)(expr curved, w, col, dash) =
  p = a.c ..
  (1/2 [a.c,b.c] + curved*unitvector(b.c-a.c) rotated 90)
  .. b.c;
  pp := p cutbefore bpath.a cutafter bpath.b;
  path ppp;
  ppp := pp cutbefore (fullcircle scaled 1mm shifted point 0 of pp);
  draw ppp
    withcolor col withpen pencircle scaled w dashed dash;
  draw diag_arrow_head (pp, length(pp))
    withcolor col withpen pencircle scaled w;
  draw diag_arrow_head(ppp, 0)
    withcolor col withpen pencircle scaled w;
enddef;

vardef diag_draw_arrow_inj(suffix a,b)(expr curved, w, col, dash) =
  p = a.c ..
  (1/2 [a.c,b.c] + curved*unitvector(b.c-a.c) rotated 90)
  .. b.c;
  pp := p cutbefore bpath.a cutafter bpath.b;
  path ppp;
  ppp := pp cutbefore (fullcircle scaled 1mm shifted point 0 of pp);
  draw ppp
    withcolor col withpen pencircle scaled w dashed dash;
  draw diag_arrow_head (pp, length(pp))
    withcolor col withpen pencircle scaled w;
  save u,A,B,C;
  pair u,A,B,C;
  A := point 0 of ppp;
  u := unitvector(direction 0 of ppp);
  B := A + ahlength*(-u) rotated (-ahangle);
  C := A + 2 ahlength*sind(ahangle)*u rotated 90;
  draw C {-u} .. B .. A {u}
  withcolor col withpen pencircle scaled w dashed dash;
enddef;

def diag_draw_arrow_mapsto(suffix a,b)(expr curved, w, col, dash) =
  p = a.c ..
  (1/2 [a.c,b.c] + curved*unitvector(b.c-a.c) rotated 90)
  .. b.c;
  pp := p cutbefore bpath.a cutafter bpath.b;
  draw pp
    withcolor col withpen pencircle scaled w dashed dash;
  draw diag_arrow_head (pp, length(pp))
    withcolor col withpen pencircle scaled w;
  draw diag_arrow_bar (pp, 0)
    withcolor col withpen pencircle scaled w;
enddef;

def diag_draw_arrow_half_dotted(suffix a,b)(expr curved, w, col, dash) =
  p = a.c ..
  (1/2 [a.c,b.c] + curved*unitvector(b.c-a.c) rotated 90)
  .. b.c;
  pp := p cutbefore bpath.a cutafter bpath.b;
  draw subpath(0,1) of pp
    withcolor col withpen pencircle scaled w dashed withsmalldots;
  draw subpath(1,2) of pp
    withcolor col withpen pencircle scaled w;
  draw diag_arrow_head (pp, length(pp))
    withcolor col withpen pencircle scaled w;
enddef;

%% Fin des fl�ches

def color_to_string (expr a) =
  "("&
    decimal(redpart a)
    &","&
    decimal(greenpart a)
    &","&
    decimal(bluepart a)
    &")"
enddef;

def enddiag =
  save i,j,k,l,mm,a,A,p,b;
  for i=0 upto _diag_x_max:
    for j=0 upto _diag_y_max:
      if known _diag[i][j]:
        circleit.a[i][j]( _diag[i][j] );
        a[i][j].dx = a[i][j].dy;
        a[i][j].c = 1cm * (i,-j);
        drawunboxed( a[i][j] );
      fi;
    endfor;
  endfor;
  for m=0 upto _diag_ar_n:
    % V�rifier que le but existe
    i := xpart _diag_ar_source[m];
    j := ypart _diag_ar_source[m];
    k := xpart _diag_ar_but[m];
    l := ypart _diag_ar_but[m];

    % On trace la fl�che. Le chemin est mis dans la variable p.
    path p,pp;
    if unknown _diag_ar_shape[m]:  _diag_ar_shape[m]  := "default" fi;
    if unknown _diag_ar_color[m]:  _diag_ar_color[m]  := black     fi;
    if unknown _diag_ar_width[m]:  _diag_ar_width[m]  := .5bp      fi;
    if unknown _diag_ar_curved[m]: _diag_ar_curved[m] := 0         fi;
    if unknown _diag_ar_dashed[m]: _diag_ar_dashed[m] := notdashed fi;
    % On ne peut PAS utiliser m dans une cha�ne ce caract�res que l'on donne
    % � scantokens, car m est une variable de boucle. C'est vraiment sp�cial,
    % une variable de boucle.
    mm := m;
    scantokens(
      "diag_draw_arrow_"& _diag_ar_shape[m]
      &"("
        &"a[i][j], a[k][l],_diag_ar_curved[mm],_diag_ar_width[mm],"
        &"_diag_ar_color[mm],_diag_ar_dashed[mm]"
        &");"
      );

    % On �crit des choses au dessus ou au dessous des fl�ches
    pair A;
    A = point 1/2 length(p) of p;
    if known _diag_ar_up[m]:
      boxit.b[m](_diag_ar_up[m]);
      b[m].c = A + 4bp*unitvector(direction 1/2 length(p) of p rotated 90);
      drawunboxed(b[m]);
    fi;
    if known _diag_ar_down[m]:
      boxit.c[m](_diag_ar_down[m]);
      c[m].c = A + 4bp*unitvector(direction 1/2 length(p) of p rotated -90);
      drawunboxed(c[m]);
    fi;
  endfor;
  endgroup;
enddef;

  begindiag;
    node "A";
      rarrowto(1,0, "above" => "a",
               "shape" => "middle",
               "curved" => 3mm,
               "dashed" => withsmalldots);
      rarrowto(0,1, "below" => "b",
               "color" => blue,
               "shape" => "mapsto",
               "dashed" => evenly);
    node "A";
      rarrowto(1,0, "above" => "c", "width" => 1bp, "shape" => "inj");
      rarrowto(0,1, "below" => "d", "shape" => "mono");
    node "A";
    nextline;
    node "A";
      rarrowto(1,0, "below" => "e", "shape" => "epi");
    node "A";
      rarrowto(1,-1, "below" => "f", "curved" => -3mm, "shape" => "half_dotted");
  enddiag;
endfig;
end;
