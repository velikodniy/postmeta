input plain;
vardef TEX primary s = s infont defaultfont scaled defaultscale enddef;
beginfig(192)
  vardef mylabel(expr pic, p, t) =
    save A,a; pair A; numeric a;
    a := angle(direction t of p rotated 90);
    show(a);
    a := a + 45/2;
    if a>180: a := a - 360 fi;
    save ll, lr, ul, ur;
    pair ul,ur,ll,lr;
    ll := llcorner pic;
    lr := lrcorner pic;
    ul := ulcorner pic;
    ur := urcorner pic;
    A = point t of p +
        8bp * unitvector(direction t of p) rotated 90;
    label(pic shifted ll, A +
      if     (a >=    0) and (a <=   45): 1/2(ur-ul)
      elseif (a >=   45) and (a <=   90): 1/2(ur-ul) + 1/2(ur-lr)
      elseif (a >=   90) and (a <=  135): 1/2(ur-lr)
      elseif (a >=  135) and (a <=  180): 1/2(ll-lr) + 1/2(ur-lr)
      elseif (a >= -180) and (a <= -135): 1/2(ll-lr)
      elseif (a >= -135) and (a <=  -90): 1/2(ll-ul) + 1/2(ll-lr)
      elseif (a >=  -90) and (a <=  -45): 1/2(ll-ul)
      elseif (a >=  -45) and (a <=    0): 1/2(ll-ul) - 1/2(ll-lr)
      else: hide(show "BUG") (0,0)
      fi);
    draw A withpen pencircle scaled 2bp withcolor red;
  enddef;
  path p; u:=1cm;
  p = (0,0)..(-u,u)..(u,u);
  p := reverse fullcircle scaled 2u;
  draw p;
  for i=0 step length(p)/10 until length(p):
    draw point i of p withpen pencircle scaled 4bp;
    mylabel(TEX decimal(i),p,i);
  endfor;
endfig;
end;
