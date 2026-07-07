input plain;
beginfig(90)
    draw fullcircle scaled 1cm;
    draw fullcircle scaled 5mm shifted (1cm*dir45);
    draw fullcircle scaled 5mm shifted (1cm*dir135);
    picture mypicture;
    mypicture := currentpicture;
    currentpicture := nullpicture;
    draw mypicture;
    draw mypicture shifted (1mm,1mm);
    draw mypicture shifted (2mm,2mm);

endfig;
end;
