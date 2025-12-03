#lang algol60

begin
  comment data definitions, values for ExprC;
  integer TAGNumC; real n;
  integer TAGIdC; integer id;
  integer TAGIfC; integer testval, thenval, otherwiseval;
  integer TAGLamC; integer argPtr, bodyPtr;
  integer TAGAppC; integer funPtr, argsPtr;
  integer TAGStrC; integer strPtr;
  integer TAGPrimC; integer primCode;

  comment each tag is assigned a number;
  TAGNumC  := 1;
  TAGIdC   := 2;
  TAGIfC   := 3;
  TAGLamC  := 4;
  TAGAppC  := 5;
  TAGStrC  := 6;
  TAGPrimC := 7;

end
