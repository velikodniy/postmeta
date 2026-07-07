input plain;
beginfig(107)
  u:=5mm;
  path p;
  p = (0,0) {curl 0} .. (u,2u) .. (2u,1.5u)
      .. (3u,2u) .. {curl 0} (4u,0);
  draw subpath(0,1) of p withcolor red;
  draw subpath(1,2) of p withcolor green;
  draw subpath(2,3) of p withcolor blue;
  draw subpath(3,3.5) of p dashed evenly;
  draw subpath(3.5,4) of p dashed withdots;

endfig;
end;
