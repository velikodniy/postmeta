input plain;
beginfig(209)
u:=1cm;

def milieu (expr s, ss, n) =
  if n<>0:
    for i="A","BA","BBA":
      milieu(s&i, ss, n-1);
    endfor;
  else:
    dessine(s&ss);
  fi;
enddef;

def doit(expr N) =
  for n=1 upto N:
    for i="A","BA","BBA":
      for j="","B","BB":
        milieu(i,j,n-1);
      endfor;
    endfor;
  endfor;
  milieu("","",0);
enddef;

vardef A(expr a) =
  save x,y,n;
  numeric x,y,n;
  x := xpart a;
  y := ypart a;
  n:=x*x+y*y;
  (-x/n, y/n)
enddef;

vardef B(expr a) =
  save x,y,n;
  numeric x,y,n;
  x := 1 + xpart a;
  y := ypart a;
  n := x*x+y*y;
  (-x/n, y/n)
enddef;

def dessine(expr s) =
  _dessine(s, dir(60),  up,       dir(120));
  _dessine(s, dir(60),  dir(31),  dir(2));
  _dessine(s, dir(120), dir(149), dir(178));
enddef;

def _dessine(expr s, a,b,c) =
  pair p[];
  p[0] := a;
  p[1] := b;
  p[2] := c;

  for i=0 upto length(s)-1:
    if (substring(i,i+1) of s) = "A":
        for j=0 upto 2: p[j] := A( p[j] ); endfor;
    elseif (substring(i,i+1) of s) = "B":
        for j=0 upto 2: p[j] := B( p[j] ); endfor;
    else: show("Ceci n'est pas un g�n�rateur : "&substring(i,i+1) of s)
    fi;
  endfor;
  if (xpart p[0] < 2) and (xpart p[0] > -2) and
     (xpart p[2] > -2) and (xpart p[2] < 2) and
     (ypart p[0] < 2) and (ypart p[2] < 2):
    draw ( p[0] .. p[1] .. p[2] ) scaled u;
  fi;

enddef;

  fill (dir(60) .. up .. dir(120) --
        (dir120+up) -- (dir60+up) -- cycle)  scaled u
       withcolor red+green;
  doit(7);
  draw (u*dir(60)) withpen pencircle scaled 4bp;
  draw (0,u) withpen pencircle scaled 4bp;
  draw (u*dir(60) -- u*dir(60)+u*up) shifted (0u,0);
  draw (u*dir(60) -- u*dir(60)+u*up) shifted (1u,0);
  draw (u*dir(60) -- u*dir(60)+u*up) shifted (-u,0);
  draw (u*dir(60) -- u*dir(60)+u*up) shifted (-2u,0);
endfig;
end;
