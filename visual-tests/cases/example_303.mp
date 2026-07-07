input plain;
vardef TEX primary s = s infont defaultfont scaled defaultscale enddef;
beginfig(303)
   draw TEX( "Nous sommes le "&
             decimal(day)   &"/"&
             decimal(month) &"/"&
             decimal(year) &"."    );

endfig;
end;
