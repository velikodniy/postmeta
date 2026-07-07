input plain;
beginfig(237)
path _myfill_p;

def myfill expr p =
  _myfill_p := p;
  _myfill
enddef;

def _myfill text t =
  fill _myfill_p t;
  draw _myfill_p t withcolor red;
enddef;

  myfill fullcircle scaled 1cm withcolor .8white withpen pencircle scaled 2bp;
endfig;
end;
