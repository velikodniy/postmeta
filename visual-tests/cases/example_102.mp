input plain;
vardef TEX primary s = s enddef;
beginfig(102)
  pair A,B,C;
  A=(0,0); B=(3cm,0); C=(1cm,2cm);
  draw A--B--C--cycle;
  label.llft(TEX decimal(angle(C-A)-angle(B-A)), A);
  label.lrt(TEX decimal(angle(A-B)-angle(C-B)), B);
  label.urt(TEX decimal(angle(B-C)-angle(A-C)), C);
endfig;
end;
