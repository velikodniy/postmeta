input plain;
input graph;
vardef TEX primary s = s infont defaultfont scaled defaultscale enddef;
beginfig(295)
  % La l�gende
  color couleur[];
  couleur[0] := red;
  couleur[1] := green;
  couleur[2] := blue;
  picture p[], legende;
  legende := nullpicture;
  for i=0 upto 2:
    p[i] := nullpicture;
    addto p[i] also TEX("Courbe " & decimal(i+1))
               withcolor couleur[i];
    addto legende doublepath ( (0,0)--(5mm,0) )
                  shifted (0, -5mm*i)
                  withpen currentpen withcolor couleur[i];
    addto legende also p[i]
                  shifted 1/2(lrcorner p[i] - ulcorner p[i])
                  shifted (0, -5mm*i);
  endfor;
  % Les courbes
  draw begingraph(3cm,2cm)
    for i=1 upto 3:
      gdraw "data" & decimal(i) withcolor couleur[i-1];
    endfor;
    glabel.top(legende,OUT);
  endgraph;
endfig;
end;
