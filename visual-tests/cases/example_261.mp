input plain;
input boxes;
let OLD_beginbox_ = beginbox_;
let OLD_boxit = boxit;
let OLD_sizebox_ = sizebox_;
let OLD_clearb_ = clearb_;
beginfig(261)
  % Les lignes suivantes n'ont pas l'effet escompt�...
  let beginbox_ = OLD_beginbox_;
  let boxit     = OLD_boxit;
  let sizebox_  = OLD_sizebox_;
  let clearb_   = OLD_clearb_;

  % On recopie donc les d�finitions initiales des macros que l'on a modifi�es...
  extra_beginfig := "";
  extra_endfig   := "";
  input boxes;

  % Et on regarde sur un exemple si �a marche...
  draw (0,0) -- (5cm,0) withcolor red;
  boxjoin(b.c - a.c = (1cm,0));
  boxit a (btex a etex);
  boxit b (btex b etex);
  boxit c (btex c etex);
  boxit d (btex d etex);
  boxit e (btex e etex);
  drawboxed(a,b,c,d,e);
endfig;
end;
