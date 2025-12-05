#lang algol60
begin
  comment "============================== BEGIN AST REPRESENTATION ==============================";
  integer array coreType, firstChild, nextSibling [0:999];
  
  comment "Store the content of NumC and IdC nodes";
  real array numcContent [0:999];
  comment "NOTE: identifiers are represented as integers, and therefore restricted to one character symbols";
  integer array idcContent [0:999];

  integer array primcContent [0:999];
  comment "Implement functions that abtract away the buffer details for LamC and AppC nodes"

  comment "Store arg list of symbols for LamC";
  integer array lamcBody [0:999]; comment "Points to the body of this LamC in the AST";
  integer array lamcStartPos [0:999]; comment "Points to where in lamcArgBuffer the arg list starts";
  integer array lamcNumArgs [0:999];  comment "Number of args for this LamC"
                                      comment "(StartPos and NumArgs are parallel with the rest of the AST)";
  integer array lamcArgBuffer [0:999]; comment "Contains the arg symbols themselves. this will be the list of symbols";
  integer nextLamcArgPos;  comment "Next free position in lamcArgBuffer"

  comment "Store ASCII character codes for StrC";
  integer array strcStartPos [0:999];
  integer array strcLength [0:999];
  integer array strcCharBuffer [0:999];
  integer nextStrcCharPos; comment "Next free position in strcCharBuffer"
  
  comment "Store arg list of AST indices for AppC";
  integer array appcFun [0:999]; comment "Points to the function being applied in the AST";
  integer array appcStartPos [0:999];
  integer array appcNumArgs [0:999];
  integer array appcArgBuffer [0:999];  comment "Contains the AST indices of argument expressions";
  integer nextAppcArgPos;

  integer nextFreePos;
  integer numcCode, idcCode, ifcCode, lamcCode, appcCode, strcCode;

  comment "Add a core type node to the AST"
  comment "typeCode: integer code representing the type of core node to add"
  comment "returns: index in coreType array where the new node was added";
  integer procedure addCoreType(typeCode);
    integer typeCode;
  begin
    integer currPos;
    currPos := nextFreePos;
    coreType[currPos] := typeCode;
    firstChild[currPos] := -1;
    nextSibling[currPos] := -1;
    nextFreePos := currPos + 1;
    addCoreType := currPos
  end;

  comment "Add a instantiate a parent-child relationship in the AST"
  comment "parent: index in coreType array of the parent node"
  comment "child: index in coreType array of the child node to add";
  procedure addChild(parent, child);
    integer parent, child;
  begin
    if firstChild[parent] = -1
      then firstChild[parent] := child
    else
      begin
      integer sibling;
      comment "Traverse to the end of the siblings"
      comment "Syntax: for <variable> := <initial> while <condition> do";
        for sibling := firstChild[parent] while sibling != -1 do
          sibling := nextSibling[sibling];

        nextSibling[sibling] := child
      end
  end;

  integer procedure addIfC(testNode, thenNode, elseNode);
    integer testNode, thenNode, elseNode;
  begin
    integer ifcNode;
    ifcNode := addCoreType(ifcCode);
    addChild(ifcNode, testNode);
    addChild(ifcNode, thenNode);
    addChild(ifcNode, elseNode);

    addIfC := ifcNode
  end;

  comment "Get the index in coreType array of the pos-th sibling of the parent node"
  comment "pos is 0-based (0 means first child)"
  comment "NOTE: You should not call this function directly";
  integer procedure privateGetSibling(parent, pos);
    integer parent, pos;
  begin
    integer sibling;
    for sibling := firstChild[parent] while pos > 0 do
      begin
        sibling := nextSibling[sibling];
        pos := pos - 1
      end;
    privateGetSibling := sibling
  end;

  comment "Get the type code of the core node at AST index idx"
  comment "idx: index in AST"
  comment "returns: integer code representing the type of core node at that index";
  integer procedure getTypeCode(idx);
    integer idx;
  begin
    getTypeCode := coreType[idx]
  end;

  comment "Set the content of the NumC at AST index idx"
  comment "idx: index in AST"
  comment "val: real value to store";
  procedure setNumC(idx, val);
    integer idx;
    real val;
  begin
    numcContent[idx] := val
  end;

  comment "Set the content of the IdC at AST index idx"
  comment "idx: index in AST"
  comment "symbol: integer value representing a symbol to store";
  procedure setIdC(idx, symbol);
    integer idx, symbol;
  begin
    idcContent[idx] := symbol
  end;

  comment "Get the content of the NumC at AST index idx"
  comment "idx: index in AST"
  comment "returns: real value stored at that index";
  real procedure getNumC(idx);
    integer idx;
  begin
    getNumC := numcContent[idx]
  end;

  comment "Get the content of the IdC at AST index idx"
  comment "idx: index in AST"
  comment "returns: integer value stored at that index which represents a symbol";
  integer procedure getIdC(idx);
    integer idx;
  begin
    getIdC := idcContent[idx]
  end;

  comment "PrimC functions";
  procedure setPrimC(idx, symbol);
     integer idx, symbol;
  begin
     primcContent[idx] := symbol
  end;

  integer procedure getPrimC(idx);
     integer idx;
  begin
     getPrimC := primcContent[idx]
  end;

  comment "Get the 'test' condition of the IfC at AST index idx"
  comment "fc: firstChild array"
  comment "ns: nextSibling array"
  comment "idx: index in AST"
  comment "returns: index in AST of the test condition node";
  integer procedure getIfCTest(fc, ns, idx);
    integer idx;
    integer array fc, ns;
  begin
    getIfCTest := privateGetSibling(fc, ns, idx, 0)
  end;

  comment "Get the 'then' branch of the IfC at AST index idx"
  comment "fc: firstChild array"
  comment "ns: nextSibling array"
  comment "idx: index in AST"
  comment "returns: index in AST of the 'then' branch node";
  integer procedure getIfCThen(fc, ns, idx);
    integer idx;
    integer array fc, ns;
  begin
    getIfCThen := privateGetSibling(fc, ns, idx, 1)
  end;

  comment "Get the 'else' branch of the IfC at AST index idx"
  comment "fc: firstChild array"
  comment "ns: nextSibling array"
  comment "idx: index in AST"
  comment "returns: index in AST of the 'else' branch node";
  integer procedure getIfCElse(fc, ns, idx);
    integer idx;
    integer array fc, ns;
  begin
    getIfCElse := privateGetSibling(fc, ns, idx, 2)
  end;

comment "===================  LamC Functions  ===================";
  integer procedure addLamC(argSymbols, numArgs, bodyNode);
     integer numArgs, bodyNode;
     integer array argSymbols;
  begin
     integer lamcNode, i, bufferStart;

     comment "1. Create the LamC node in the AST";
     lamcNode := addCoreType(lamcCode);

     comment "2. Store reference to the body expression";
     lamcBody[lamcNode] := bodyNode;

     comment "3. Where args will starts in the shared buffer";
     bufferStart := nextLamcArgPos;
     lamcStartPos[lamcNode] := bufferStart;

     comment "4. How many args this lambda has";
     lamcNumArgs[lamcNode] := numArgs;

     comment "5. Copy argument symbols into shared buffer";
     for i := 0 step 1 until numArgs -1 do
        lamcArgBuffer[bufferStart + i] := argSymbols[i];

     comment "6. Adavnce the next free position in buffer";
     nextLamcArgPos := nextLamcArgPos + numArgs;

     comment "7. Returns the AST index of the new LamC node";
     addLamC := lamcNode
  end;

  comment "Get the body AST index of a LamC node";
  integer procedure getLamCBody(idx);
     integer idx;
  begin
     getLamCBody := lamcBody[idx]
  end;

  comment "Get the num of args of a lamC node";
  integer procedure getLamCNumArgs(idx);
     integer idx;
  begin
     getLamCNumArgs := lamcNumArgs[idx];
  end;

  comment "Get the n-th argument symbol of a LamC node";
  integer procedure getLamCArg(idx, n);
     integer idx, n;
  begin
     integer startPos;
     startPos := lamcStartPos[idx];
     getLamCArg := lamcArgBuffer[startPos + n]
  end;

  comment "=============  AppC Functions ================";
  integer procedure addAppC(funNode, argNodes, numArgs);
    integer funNode, numArgs;
    integer array argNodes;

  begin
    integer appcNode, i, bufferStart;

    appcNode := addCoreType(appcCode);

    comment "Store reference to the function expression";
    appcFun[appcNode] := funNode;

    comment "Where args will start in the shared buffer";
    bufferStart := nextAppcArgPos;
    appcStartPos[appcNode] := bufferStart;

    comment "How many args this app has";
    appcNumArgs[appcNode] := numArgs;

    comment "Copy argument AST indices into shared buffer";
    for i := 0 step 1 until numArgs - 1 do
       appcArgBuffer[bufferStart + i] := argNodes[i];

    nextAppcArgPos := nextAppcArgPos + numArgs;
    addAppC := appcNode
  end;

 comment "Get the function AST index of an AppC node";
  integer procedure getAppCFun(idx);
     integer idx;
  begin
     getAppCFun := appcFun[idx]
  end;

  comment "Get the number of arguments of an AppC node";
  integer procedure getAppCNumArgs(idx);
     integer idx;
  begin
     getAppCNumArgs := appcNumArgs[idx]
  end;

  comment "Get the n-th argument AST index of an AppC node";
  integer procedure getAppCArg(idx, n);
     integer idx, n;
  begin
     integer startPos;
     startPos := appcStartPos[idx];
     getAppCArg := appcArgBuffer[startPos + n]
  end;


  comment "=============  StrC Functions ================";
  integer procedure addStrC(asciiCodes, length);
    integer length;
    integer array asciiCodes;

  begin
    integer strcNode, i, bufferStart;
    strcNode := addCoreType(strcCode);
    bufferStart := nextStrcCharPos;
    strcStartPos[strcNode] := bufferStart;
    strcLength[strcNode] := length;

    comment "Copy ASCII characters into shared buffer";
    for i := 0 step 1 until length - 1 do
       strcCharBuffer[bufferStart + i] := asciiCodes[i];

    nextStrcCharPos := nextStrcCharPos + length;

    addStrC := strcNode
  end;

  comment "Length of StrC string";
  integer procedure getStrCLength(idx);
      integer idx;
  begin
      getStrCLength := strcLength[idx]
  end;

  comment "Get the n-th character of a StrC string";
  integer procedure getStrCChar(idx, n);
     integer idx, n;
  begin
     integer startPos;
     startPos := strcStartPos[idx];
     getStrCChar := strcCharBuffer[startPos + n]
  end;

  comment "Clear the AST representation"
  comment "NOTE: this function is extremely slow to use idk why";
  procedure clearAST;
  begin
    integer i;
    for i := 0 while i <= 999 do
      begin
        coreType[i] := -1;
        firstChild[i] := -1;
        nextSibling[i] := -1;
        numcContent[i] := 0.0;
        idcContent[i] := -1;
        i := i + 1
      end;
    nextFreePos := 0;
    nextLamcArgPos := 0;
    nextStrcCharPos := 0
  end;

  comment "============================== END AST REPRESENTATION =============================="

  comment "============================== BEGIN VALUE REPRESENTATION ==========================";
  integer array valueType [0:999];
  real array numVContent [0:999];
  integer array boolVContent [0:999];

  comment "StrV uses same buffer pattern as StrC";
  integer array strVStartPos, strVLength [0:999];
  integer array strVCharBuffer [0:999];
  integer nextStrVCharPos;

  comment "CloV - closure values";
  integer array cloVParamsStart, cloVNumParams [0:999];
  integer array cloVParamsBuffer [0:999];
  integer array cloVBody [0:999];
  integer array cloVEnv [0:999];
  integer nextCloVParamsPos;

  comment "PrimV - primitive function values";
  integer array primVSymbol [0:999];

  integer nextValuePos;
  integer numvCode, boolvCode, strvCode, clovCode, primvCode;
  integer procedure createNumV(n);
    real n;
  begin
    integer valIdx;
    valIdx := nextValuePos;
    valueType[valIdx] := numvCode;
    numVContent[valIdx] := n;
    nextValuePos := nextValuePos + 1;
    createNumV := valIdx
  end;

  real procedure getNumV(valIdx);
    integer valIdx;
  begin
    getNumV := numVContent[valIdx]
  end;

  integer procedure createBoolV(b);
     integer b;
  begin
     integer valIdx;
     valIdx := nextValuePos;
     valueType[valIdx] := boolvCode;
     boolVContent[valIdx] := b;
     nextValuePos := nextValuePos + 1;
     createBoolV := valIdx
  end;
  
    integer procedure getBoolV(valIdx);
    integer valIdx;
  begin
    getBoolV := boolVContent[valIdx]
  end;

comment "==================== StrV Functions ====================";
integer procedure createStrV(asciiCodes, length);
  integer length;
  integer array asciiCodes;
begin
  integer valIdx, i, bufferStart;
  valIdx := nextValuePos;
  valueType[valIdx] := strvCode;
  
  bufferStart := nextStrVCharPos;
  strVStartPos[valIdx] := bufferStart;
  strVLength[valIdx] := length;
  
  comment "Copy ASCII characters into StrV buffer";
  for i := 0 step 1 until length - 1 do
    strVCharBuffer[bufferStart + i] := asciiCodes[i];
  
  nextStrVCharPos := nextStrVCharPos + length;
  nextValuePos := nextValuePos + 1;
  createStrV := valIdx
end;

  integer procedure getStrVLength(valIdx);
    integer valIdx;
  begin
    getStrVLength := strVLength[valIdx]
  end;

  integer procedure getStrVChar(valIdx, n);
    integer valIdx, n;
  begin
    integer startPos;
    startPos := strVStartPos[valIdx];
    getStrVChar := strVCharBuffer[startPos + n]
  end;
  
  comment "==================== CloV Functions ====================";
  integer procedure createCloV(paramSymbols, numParams, bodyNode, envIdx);
    integer numParams, bodyNode, envIdx;
    integer array paramSymbols;
  begin
    integer valIdx, i, bufferStart;
    valIdx := nextValuePos;
    valueType[valIdx] := clovCode;
    
    comment "Store body and environment references";
    cloVBody[valIdx] := bodyNode;
    cloVEnv[valIdx] := envIdx;
    
    comment "Store parameters in buffer";
    bufferStart := nextCloVParamsPos;
    cloVParamsStart[valIdx] := bufferStart;
    cloVNumParams[valIdx] := numParams;
    
    for i := 0 step 1 until numParams - 1 do
      cloVParamsBuffer[bufferStart + i] := paramSymbols[i];
    
    nextCloVParamsPos := nextCloVParamsPos + numParams;
    nextValuePos := nextValuePos + 1;
    createCloV := valIdx
  end;

  integer procedure getCloVBody(valIdx);
    integer valIdx;
  begin
    getCloVBody := cloVBody[valIdx]
  end;

  integer procedure getCloVEnv(valIdx);
    integer valIdx;
  begin
    getCloVEnv := cloVEnv[valIdx]
  end;

  integer procedure getCloVNumParams(valIdx);
    integer valIdx;
  begin
    getCloVNumParams := cloVNumParams[valIdx]
  end;

  integer procedure getCloVParam(valIdx, n);
    integer valIdx, n;
  begin
    integer startPos;
    startPos := cloVParamsStart[valIdx];
    getCloVParam := cloVParamsBuffer[startPos + n]
  end;
  
  comment "==================== PrimV Functions ====================";
  integer procedure createPrimV(symbol);
    integer symbol;
  begin
    integer valIdx;
    valIdx := nextValuePos;
    valueType[valIdx] := primvCode;
    primVSymbol[valIdx] := symbol;
    nextValuePos := nextValuePos + 1;
    createPrimV := valIdx
  end;

  integer procedure getPrimV(valIdx);
    integer valIdx;
  begin
    getPrimV := primVSymbol[valIdx]
  end;

  comment "==================== Value Type Checking ====================";
  Boolean procedure isNumV(valIdx);
    integer valIdx;
  begin
    isNumV := valueType[valIdx] = numvCode
  end;

  Boolean procedure isBoolV(valIdx);
    integer valIdx;
  begin
    isBoolV := valueType[valIdx] = boolvCode
  end;

  Boolean procedure isStrV(valIdx);
    integer valIdx;
  begin
    isStrV := valueType[valIdx] = strvCode
  end;

  Boolean procedure isCloV(valIdx);
    integer valIdx;
  begin
    isCloV := valueType[valIdx] = clovCode
  end;

  Boolean procedure isPrimV(valIdx);
    integer valIdx;
  begin
    isPrimV := valueType[valIdx] = primvCode
  end;
  
comment "Initialize AST representation";
nextFreePos := 0;
nextLamcArgPos := 0;
nextStrcCharPos := 0;
nextAppcArgPos := 0;  comment 


numcCode := 0;
idcCode := 1;
ifcCode := 2;
lamcCode := 3;
appcCode := 4;
strcCode := 5;

comment "Initialize Value representation";
nextValuePos := 0;
nextStrVCharPos := 0;  
nextCloVParamsPos := 0;

comment "Value type codes - ADD THESE!";
numvCode := 100;
boolvCode := 101;
strvCode := 102;
clovCode := 103;
primvCode := 104;


    

  comment "============================== AST Node Examples ============================"";
  begin 
    comment "The following is equivalent to instantiating (IfC (NumC 1) (NumC 2) (NumC 3))";
    integer ifcNode, num1, num2, num3;
    
    num1 := addCoreType(numcCode);
    setNumC(num1, 1.0);
    num2 := addCoreType(numcCode);
    setNumC(num2, 2.0);
    num3 := addCoreType(numcCode);
    setNumC(num3, 3.0);
    ifcNode := addIfC(num1, num2, num3);
  end;

  begin
    comment "LamC Example - (lambda () 3)";
    integer lambdaNode, bodyNode;
    integer retrievedBody, retrievedNumArgs;
    integer array emptyParams[0:0];
  
    bodyNode := addCoreType(numcCode);
    setNumC(bodyNode, 3.0);

    lambdaNode := addLamC(emptyParams, 0, bodyNode);

    retrievedBody := getLamCBody(lambdaNode);
    retrievedNumArgs := getLamCNumArgs(lambdaNode)
  end;

  begin
    comment "AppC Example - ((lambda (x) : x) 5)";
    integer lambdaNode, bodyNode, argNode, appNode;
    integer array params[0:0];
    integer array args[0:0];
    integer retrievedFun, retrievedNumArgs, retrievedArg0;

    comment "Create the lambda (lambda (x) : x)";
    params[0] := 120; comment "x in ascii is 120";
    bodyNode := addCoreType(idcCode);
    setIdC(bodyNode, 120); comment "body is x";
    lambdaNode := addLamC(params, 1, bodyNode);

    argNode := addCoreType(numcCode);
    setNumC(argNode, 5.0);

    args[0] := argNode;
    appNode := addAppC(lambdaNode, args, 1);
  end;

  begin
    comment"StrC Example - "hello"";
    integer strcNode;
    integer array helloChars[0:4];
    integer retrievedLength, char0, char1, char2, char3, char4;

    helloChars[0] := 104; comment "h";
    helloChars[1] := 101; comment "e";
    helloChars[2] := 108; comment "l";
    helloChars[3] := 108; comment "l";
    helloChars[4] := 111; comment "o";

   strcNode := addStrC(helloChars, 5);

   retrievedLength := getStrCLength(strcNode);
   char0 := getStrCChar(strcNode, 0);
   char1 := getStrCChar(strcNode, 1)
  end
  
end
