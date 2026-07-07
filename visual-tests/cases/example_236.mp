input plain;
beginfig(236)
  def reddraw text t = draw t withcolor red enddef;
  draw (0,0) -- (2cm,0);
  reddraw (0,0) -- (2cm,5mm) withpen pencircle scaled 2bp;

endfig;
end;
