input plain;
beginfig(59)
  u:=1cm;
  draw (0,u)         {right}    .. tension 4 ..
       ( u*dir -150 ){dir 120}  .. tension 4 ..
       ( u*dir -30  ){dir -120} .. tension 4 ..
  cycle;
endfig;
end;
