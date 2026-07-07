input plain;
beginfig(188)
  def drawwhitearrow expr p = _apth:=p; _finwhitearr enddef;

  def _finwhitearr text t =
    draw _apth t;
    fill arrowhead _apth  t withcolor white;
    draw arrowhead _apth  t
  enddef;

  u:=1cm;
  drawwhitearrow (0,0) .. (-u,u) .. (u,u);
endfig;
end;
