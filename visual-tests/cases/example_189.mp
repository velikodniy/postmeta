input plain;
beginfig(189)
  def draw_white_arrow expr p = _apth:=p; _fin_white_arr enddef;
  def _fin_white_arr text t =
    draw _apth t;
    fill arrowhead _apth withcolor white;
    draw arrowhead _apth  t
  enddef;

  def draw_middle_arrow expr p = _apth:=p; _fin_middle_arr enddef;
  def _fin_middle_arr text t =
    draw _apth t;
    filldraw arrowhead_middle _apth  t
  enddef;
  vardef arrowhead_middle expr p =
    save A,u; pair A,u;
    A := point (arctime (.5arclength p) of p) of p;
    u := unitvector(direction (arctime (.5arclength p) of p) of p);
    A -- (A - ahlength*u rotated (.5ahangle) ) --
    (A - ahlength*u rotated (-.5ahangle) ) -- cycle
  enddef;

  def draw_middle_white_arrow expr p = _apth:=p; _fin_middle_white_arr enddef;
  let draw_white_middle_arrow = draw_middle_white_arrow;
  def _fin_middle_white_arr text t =
    draw _apth t;
    fill arrowhead_middle _apth  t withcolor white;
    draw arrowhead_middle _apth  t
  enddef;

  def draw_other_arrow expr p = _apth:=p; _fin_other_arr enddef;
  def _fin_other_arr text t =
    draw _apth t;
    draw arrowhead_other _apth  t
  enddef;
  vardef arrowhead_other expr p =
    save A,u,a,b; pair A,u; path a,b;
    A := point (length p) of p;
    u := unitvector(direction (length p) of p);
    a := A{-u} .. (A - ahlength*u rotated 30);
    b := A{-u} .. (A - ahlength*u rotated -30);
    ( a & reverse(a) & b & reverse(b) ) --cycle
  enddef;

  def draw_other_middle_arrow expr p = _apth:=p; _fin_other_middle_arr enddef;
  let draw_middle_other_arrow = draw_other_middle_arrow;
  def _fin_other_middle_arr text t =
    draw _apth t;
    draw arrowhead_other_middle _apth  t
  enddef;
  vardef arrowhead_other_middle expr p =
    save A,u,a,b; pair A,u; path a,b;
    A := point (arctime (.5arclength p) of p) of p;
    u := unitvector(direction (arctime (.5arclength p) of p) of p);
    a := A{-u} .. (A - ahlength*u rotated 30);
    b := A{-u} .. (A - ahlength*u rotated -30);
    ( a & reverse(a) & b & reverse(b) ) --cycle
  enddef;

  path p;
  p := halfcircle scaled 2cm;
  p := (0,0) .. (3cm,1cm) .. (-1cm,3cm);
  p := p scaled .3;
  draw_middle_arrow p;
  draw_white_arrow p scaled 1.3 withpen pencircle scaled 1bp;
  draw_white_middle_arrow p scaled 1.6;
  draw_other_middle_arrow p scaled 1.8 withpen pencircle scaled 1bp;
  draw_other_arrow p scaled 2 withpen pencircle scaled 1bp;
endfig;
end;
