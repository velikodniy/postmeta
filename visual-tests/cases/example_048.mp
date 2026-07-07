input plain;
beginfig(48)
  alpha := 30;
  draw (0,0) -- 2cm*dir 0;
  draw (0,0) -- 2cm*dir alpha;
  draw 1cm * dir 0 {dir 90} ..
       1cm * dir alpha {dir(90+alpha)};
endfig;
end;
