input plain;
beginfig(173)
vardef inversion (expr O,k,M) =
  if pair M:
    (O + k*unitvector(M-O)/abs(M-O))
  elseif path M:
    for i=0 step length(M)/100 until length(M):
      inversion(O,k,point i of M) ..
    endfor
    cycle
  fi
enddef;

  u:=4cm;
  path p[],A,B;

  z0 = (5u,0) rotated 10;

  A = fullcircle scaled 2u;
  B = A scaled 3;
  draw inversion( z0, 2 (u**2), A )
       withpen pencircle scaled 1pt;
  draw inversion( z0, 2 (u**2), B )
       withpen pencircle scaled 1pt;

  p0 = fullcircle scaled 2u shifted (2u,0);
  for i=0 upto 5:
    if i<>0:
      p[i] = p[i-1] rotated (360/6);
    fi;
    draw inversion( z0, 2 (u**2), p[i] );
  endfor;
endfig;
end;
