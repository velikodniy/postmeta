input plain;
input boxes;
beginfig(255)
  let OLD_beginbox_ = beginbox_;
  def beginbox_(expr pp,sp)(suffix $)(text t) =
    _n_ := str $;
    generic_declare(pair) _n.off, _n.c;
    generic_declare(string) pproc_._n, sproc_._n;
    generic_declare(picture) pic_._n;
    pproc_$:=pp; sproc_$:=sp;
    pic_$ = nullpicture;
    for _p_=t:
      pic_$:=
        if picture _p_: _p_
        else: _p_ infont defaultfont scaled defaultscale
        fi;
    endfor
    $c = $off + (.5[xpart llcorner pic_$, xpart urcorner pic_$], 0)
  enddef;

  draw (0,0) -- (5cm,0) withcolor red;
  boxjoin(b.c - a.c = (1cm,0));
  boxit a (btex a etex);
  boxit b (btex b etex);
  boxit c (btex c etex);
  boxit d (btex d etex);
  boxit e (btex e etex);
  drawunboxed(a,b,c,d,e);
endfig;
end;
