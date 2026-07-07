input plain;
beginfig(214)
  m:=50;
  pair A[], B[];
  A[0]=(0,0);
  for i=0 upto m:
    A[i+1]=(i/m*3u, (ypart A[i])+(uniformdeviate(2)-1)/m*30u);
  endfor;
  B[0]=A[0];
  B[1]=A[1];
  B[2]=A[2];
  B[3]=A[3];
  for i=4 upto m+1:
    B[i] = ( A[i-4] + A[i-3] + A[i-2] + A[i-1] + A[i])/5;
  endfor;
  for i=0 upto m:
    draw B[i]--B[i+1] withpen pencircle scaled 2pt
         withcolor .5*white;
  endfor;
  for i=0 upto m:
    draw A[i]--A[i+1];
  endfor;
  draw (0,0)--(3u,0);
endfig;
end;
