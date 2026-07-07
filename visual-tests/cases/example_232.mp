input plain;
beginfig(232)
  u:=1cm;
vardef inversion (expr O,k,M) =
  if pair M:
    (O + k*unitvector(M-O)/abs(M-O))
  elseif path M:
    for i=0 step length(M)/10 until length(M):
      hide(
        draw O--inversion(O,k,point i of M)--(point i of M);
        draw inversion(O,k,point i of M) withpen pencircle scaled 2pt;
        draw point i of M withpen pencircle scaled 2pt withcolor red;
        draw O withpen pencircle scaled 2pt;
        )
      inversion(O,k,point i of M) ..
    endfor
    cycle
  fi
enddef;

  path p[];
  p1=fullcircle scaled 2u shifted (u,0);
  p2=fullcircle scaled 2u shifted (-u,0);
  draw p1 dashed withdots scaled .25;
  draw p2 dashed withdots scaled .25;
  z0 = (.5u,2u);
  draw inversion( z0, 2 (u**2), p1 );
  draw inversion( z0, 2 (u**2), p2 );
endfig;
end;
