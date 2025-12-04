#lang algol60
begin
  comment "============================== BEGIN AST REPRESENTATION ==============================";
  integer array coreType, firstChild, nextSibling [0:999];
  
  comment "Store the content of NumC and IdC nodes";
  real array numcContent [0:999];
  comment "NOTE: identifiers are represented as integers, and therefore restricted to one character symbols";
  integer array idcContent [0:999];

  comment "TODO: implement LamC, AppC, and StrC representations w/ the buffer approach"
  comment "Implement functions that abtract away the buffer details for LamC and AppC nodes"

  comment "Store arg list of symbols for LamC";
  integer array lamcBody [0:999]; comment "Points to the body of this LamC in the AST";
  integer array lamcStartPos [0:999]; comment "Points to where in lamcArgBuffer the arg list starts";
  integer array lamcNumArgs [0:999];  comment "Number of args for this LamC"
                                      comment "(StartPos and NumArgs are parallel with the rest of the AST)";
  integer array lamcArgBuffer [0:999]; comment "Contains the arg symbols themselves";
  
  integer array strcBuffer [0:999];
  integer array strStartPos [0:999];
  integer array strNumElems [0:999];
  
  comment "Store arg list of AST indices for AppC";
  integer array appcFun [0:999]; comment "Points to the function being applied in the AST";
  integer array appcStartPos [0:999];
  integer array appcNumArgs [0:999];
  integer array appcArgBuffer [0:999];

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
    addChild(ifcNode, elseNode)
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
    nextFreePos := 0
  end;

  comment "Initialize AST representation";
  nextFreePos := 0;
  numcCode := 0;
  idcCode := 1;
  ifcCode := 2;
  lamcCode := 3;
  appcCode := 4;
  strcCode := 5;
  comment "============================== END AST REPRESENTATION ==============================";

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
  end
end