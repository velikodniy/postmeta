input plain;
beginfig(58)
  u:=1cm;
  draw (0,u)         {right}    .. tension 2 ..
       ( u*dir -150 ){dir 120}  .. tension 2 ..
       ( u*dir -30  ){dir -120} .. tension 2 ..
  cycle;
endfig;
end;
