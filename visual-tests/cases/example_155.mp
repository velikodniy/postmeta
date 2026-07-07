input plain;
beginfig(155)
  u:=1cm;
vardef f(expr x,y) = sind(x/u*180)*sind(y/u*180)*u enddef;

boolean dessine_fil_de_fer;  dessine_fil_de_fer := false;
color   dessine_couleur;     dessine_couleur    := red+green;

vardef dessine(suffix f)(expr xmin, xmax, xinc, ymin, ymax, yinc) =
  save i,j,p,dfdx,dfdy,project;
  vardef project(expr x,y,z) =
    x*(-1,-1) + y*(1,0) + z*(0,1)
  enddef;
  for i=xmin step xinc until xmax:
    for j=ymin step yinc until ymax:
      path p;
      p = project(i,j,f(i,j)) --
          project(i,j+yinc,f(i,j+yinc)) --
          project(i+xinc,j+yinc,f(i+xinc,j+yinc)) --
          project(i+xinc,j,f(i+xinc,j)) --
          cycle;
      dfdx := (f(i,j) - f(i+xinc,j))/xinc;
      dfdy := (f(i,j) - f(i,j+yinc))/yinc;
      couleur := 1/sqrt( dfdx**2 + dfdy**2 + 1);
      fill p withcolor couleur*dessine_couleur;
      if dessine_fil_de_fer: draw p fi;
    endfor
  endfor;
enddef;

  % Il faudrait pouvoir choisir diff�rents
  % types d'� �clairage �.
  vardef f(expr x,y) = sind(x/u*180)*sind(y/u*180)*u enddef;
  dessine(f,-2u,2u,.1u, -2u,2u,.1u);
endfig;
end;
