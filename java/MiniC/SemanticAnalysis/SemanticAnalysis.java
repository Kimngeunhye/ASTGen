package MiniC.SemanticAnalysis;

import MiniC.ErrorReporter;
import MiniC.StdEnvironment;
import MiniC.Scanner.SourcePos;
import MiniC.AstGen.*;

public class SemanticAnalysis implements Visitor {

  private ErrorReporter reporter;
  private ScopeStack scopeStack;
  private boolean IsFunctionBlock;
  private Type currentFunctionReturnType;

  public SemanticAnalysis(ErrorReporter reporter) {
    this.reporter = reporter;
    this.scopeStack = new ScopeStack ();
    // Here we enter the entities from the StdEnvironment into the scope stack:
    // The scope stack is on level 1 now (initial setting).
    scopeStack.enter ("int", StdEnvironment.intTypeDecl);
    scopeStack.enter ("bool", StdEnvironment.boolTypeDecl);
    scopeStack.enter ("float", StdEnvironment.floatTypeDecl);
    scopeStack.enter ("void", StdEnvironment.voidTypeDecl);
    scopeStack.enter ("getInt", StdEnvironment.getInt);
    scopeStack.enter ("putInt", StdEnvironment.putInt);
    scopeStack.enter ("getBool", StdEnvironment.getBool);
    scopeStack.enter ("putBool", StdEnvironment.putBool);
    scopeStack.enter ("getFloat", StdEnvironment.getFloat);
    scopeStack.enter ("putFloat", StdEnvironment.putFloat);
    scopeStack.enter ("getString", StdEnvironment.getString);
    scopeStack.enter ("putString", StdEnvironment.putString);
    scopeStack.enter ("putLn", StdEnvironment.putLn);
  }

  private Type typeOfDecl(AST d) {
    Type T;
    if (d == null) {
      return StdEnvironment.errorType;
    }
    assert ((d instanceof FunDecl) || (d instanceof VarDecl)
            || (d instanceof FormalParamDecl));
    if (d instanceof FunDecl) {
      T = ((FunDecl) d).tAST;
    } else if (d instanceof VarDecl) {
      T = ((VarDecl) d).tAST;
    } else {
      T = ((FormalParamDecl) d).astType;
    }
    return T;
  }

  // This function returns the element type of ArrayType AST node.
  private Type typeOfArrayType(AST d) {
    assert (d != null);
    assert (d instanceof ArrayType);
    ArrayType T = (ArrayType)d;
    return T.astType;
  }

  // This function returns true, if an operator accepts integer or
  // floating point arguments.
  //  <int> x <int> -> <sometype>
  //  <float> x <float> -> <sometype>
  private boolean HasIntOrFloatArgs (Operator op) {
    return (op.Lexeme.equals("+") ||
            op.Lexeme.equals("-") ||
            op.Lexeme.equals("*") ||
            op.Lexeme.equals("/") ||
            op.Lexeme.equals("<") ||
            op.Lexeme.equals("<=") ||
            op.Lexeme.equals(">") ||
            op.Lexeme.equals(">=") ||
            op.Lexeme.equals("==") ||
            op.Lexeme.equals("!="));
  }

  // This function returns true, if an operator accepts bool arguments.
  //  <bool> x <bool> -> <sometype>
  private boolean HasBoolArgs (Operator op) {
    return (op.Lexeme.equals("&&") ||
            op.Lexeme.equals("||") ||
            op.Lexeme.equals("!") ||
            op.Lexeme.equals("!=") ||
            op.Lexeme.equals("=="));
  }

  // This function returns true, if an operator returns a bool value.
  //  <sometype> x <sometype> -> bool
  private boolean HasBoolReturnType (Operator op) {
    return (op.Lexeme.equals("&&") ||
            op.Lexeme.equals("||") ||
            op.Lexeme.equals("!")  ||
            op.Lexeme.equals("!=") ||
            op.Lexeme.equals("==") ||
            op.Lexeme.equals("<")  ||
            op.Lexeme.equals("<=") ||
            op.Lexeme.equals(">")  ||
            op.Lexeme.equals(">="));
  }
  private Expr i2f (Expr e) {
    Operator op = new Operator ("i2f", new SourcePos());
    op.type = StdEnvironment.intType;
    UnaryExpr eAST = new UnaryExpr (op, e, new SourcePos());
    eAST.type = StdEnvironment.floatType;
    return eAST;
  }
  private int GetNrOfFormalParams(FunDecl f) {
    int NrArgs = 0;
    Decl D = f.paramsAST;
    assert ((D instanceof EmptyFormalParamDecl) ||
            (D instanceof FormalParamDeclSequence));
    if(D instanceof EmptyFormalParamDecl)
      return 0;
    while (D instanceof FormalParamDeclSequence) {
      NrArgs++;
      D = ((FormalParamDeclSequence) D).rAST;
      assert ((D instanceof EmptyFormalParamDecl) ||
              (D instanceof FormalParamDeclSequence));
    }
    return NrArgs;
  }

  private FormalParamDecl GetFormalParam (FunDecl f, int nr) {
    int fArgs = GetNrOfFormalParams(f);
    assert(fArgs >= 0);
    assert (nr <= fArgs);
    FormalParamDeclSequence S = (FormalParamDeclSequence) f.paramsAST;
    for (int i = 1; i < nr; i++) {
      assert(S.rAST instanceof FormalParamDeclSequence);
      S = (FormalParamDeclSequence) S.rAST;
    }
    assert(S.lAST instanceof FormalParamDecl);
    return (FormalParamDecl) S.lAST;
  }

  private int GetNrOfActualParams(CallExpr f) {
    int NrArgs = 0;
    Expr P = f.paramAST;
    assert ((P instanceof EmptyActualParam) ||
            (P instanceof ActualParamSequence));
    if(P instanceof EmptyActualParam)
      return 0;
    while (P instanceof ActualParamSequence) {
      NrArgs++;
      P = ((ActualParamSequence) P).rAST;
      assert ((P instanceof EmptyActualParam) ||
              (P instanceof ActualParamSequence));
    }
    return NrArgs;
  }
  private ActualParam GetActualParam (CallExpr f, int nr) {
    int aArgs = GetNrOfActualParams(f);
    Expr P = f.paramAST;
    assert(aArgs >= 0);
    assert (nr <= aArgs);
    for (int i = 1; i < nr; i++) {
      assert(P instanceof ActualParamSequence);
      P = ((ActualParamSequence) P).rAST;
    }
    assert (((ActualParamSequence) P).lAST instanceof ActualParam);
    return (ActualParam) ((ActualParamSequence) P).lAST;
  }

  private String TypeTag (Type t) {
    String l = new String("");
    if (t == null) {
      l = new String("<?>");
    } else if (t.Tequal(StdEnvironment.intType)) {
      l = new String ("<int>");
    } else if (t.Tequal(StdEnvironment.boolType)) {
      l = new String ("<bool>");
    } else if (t.Tequal(StdEnvironment.floatType)) {
      l = new String ("<float>");
    } else if (t.Tequal(StdEnvironment.stringType)) {
      l = new String ("<string>");
    } else if (t.Tequal(StdEnvironment.voidType)) {
      l = new String ("<void>");
    } else if (t instanceof ErrorType) {
      l = new String ("<error>");
    } else {
      assert(false);
    }
    return l;
  }

  private String errMsg[] = {
          "#0: main function missing",
          "#1: return type of main must be int",

          //defining occurrences of identifiers,
          //for local, global variables and for formal parameters:
          "#2: identifier redeclared",
          "#3: identifier declared void",
          "#4: identifier declared void[]",

          //applied occurrences of identifiers:
          "#5: undeclared identifier",

          //assignment statements:
          "#6: incompatible types for =",
          "#7: invalid lvalue in assignment",

          //expression types:
          "#8: incompatible type for return statement",
          "#9: incompatible types for binary operator",
          "#10: incompatible type for unary operator",

          //scalars:
          "#11: attempt to use a function as a scalar",

          //arrays:
          "#12: attempt to use scalar/function as an array",
          "#13: wrong type for element in array initializer",
          "#14: invalid initializer: array initializer for scalar",
          "#15: invalid initializer: scalar initializer for array",
          "#16: too many elements in array initializer",
          "#17: array subscript is not an integer",
          "#18: array size missing",

          //functions:
          "#19: attempt to reference a scalar/array as a function",

          //conditional expressions:
          "#20: \"if\" conditional is not of type boolean",
          "#21: \"for\" conditional is not of type boolean",
          "#22: \"while\" conditional is not of type boolean",

          //parameters:
          "#23: too many actual parameters",
          "#24: too few actual parameters",
          "#25: wrong type for actual parameter"
  };

  public void check(Program progAST) {
    visit(progAST);
    Decl mainDecl = scopeStack.retrieve("main");
    if (!(mainDecl instanceof FunDecl))
    {
      reporter.reportError(errMsg[0], "", new SourcePos());
    }
  }

  public void visit(Program x) {
    x.D.accept(this);
  }

  public void visit(EmptyDecl x) {
  }

  public void visit(FunDecl x) {
    currentFunctionReturnType = x.tAST;

    if (!scopeStack.enter(x.idAST.Lexeme, x))
    {
      reporter.reportError(errMsg[2], x.idAST.Lexeme, x.idAST.pos);
    }
    if (x.idAST.Lexeme.equals("main"))
    {
      if(!x.tAST.Tequal(StdEnvironment.intType))
      {
        reporter.reportError(errMsg[1], "", x.idAST.pos);
      }
    }
    scopeStack.openScope();
    IsFunctionBlock = true; // needed in {...}, to avoid opening a fresh scope.

    x.paramsAST.accept(this);
    x.stmtAST.accept(this);
    scopeStack.closeScope();
  }

  public void visit(TypeDecl x) {
    assert(false); // TypeDecl nodes occur only in the StdEnvironment AST.
  }

  public void visit(FormalParamDecl x) {
    if (x.astType instanceof ArrayType) {
      ((ArrayType)x.astType).astExpr.accept(this);
    }
    if(!scopeStack.enter(x.astIdent.Lexeme, x))
    {
      reporter.reportError(errMsg[2], x.astIdent.Lexeme, x.astIdent.pos);
    }
    if(x.astType.Tequal(StdEnvironment.voidType))
    {
      reporter.reportError(errMsg[3], x.astIdent.Lexeme, x.astIdent.pos   );
    }
    if(x.astType instanceof ArrayType arrayType)
    {
      if(arrayType.astType.Tequal(StdEnvironment.voidType))
      {
        reporter.reportError(errMsg[4], x.astIdent.Lexeme, x.astIdent.pos);
      }
    }
  }

  public void visit(FormalParamDeclSequence x) {
    x.lAST.accept(this);
    x.rAST.accept(this);
  }

  public void visit(EmptyFormalParamDecl x) {
  }

  public void visit(StmtSequence x) {
    x.s1AST.accept(this);
    x.s2AST.accept(this);
  }

  public void visit(AssignStmt x) {
    x.lAST.accept(this);
    x.rAST.accept(this);
    if(!(x.lAST.type.Tequal(x.rAST.type)))
    {
      reporter.reportError(errMsg[6], "", x.pos);
    }

    if(!(x.lAST instanceof VarExpr) && !(x.lAST instanceof ArrayExpr)) {
      reporter.reportError(errMsg[7], "", x.lAST.pos);
    }
  }

  public void visit(IfStmt x) {
    x.eAST.accept(this);
    if(!(x.eAST.type.Tequal(StdEnvironment.boolType)))
    {
      reporter.reportError(errMsg[20], "", x.eAST.pos);
    }
    x.thenAST.accept(this);
    if(x.elseAST != null) {
      x.elseAST.accept(this);
    }
  }

  public void visit(WhileStmt x) {
    x.eAST.accept(this);
    if(!x.eAST.type.Tequal((StdEnvironment.boolType)))
    {
      reporter.reportError(errMsg[22], "", x.eAST.pos);
    }
    x.stmtAST.accept(this);
  }

  public void visit(ForStmt x) {
    x.e1AST.accept(this);
    if(!(x.e2AST instanceof EmptyExpr)) {
      x.e2AST.accept(this);
      if(!x.e2AST.type.Tequal(StdEnvironment.boolType)) {
        reporter.reportError(errMsg[21], "", x.e2AST.pos);
      }
    }
    if(!(x.e3AST instanceof EmptyExpr)) {
      x.e3AST.accept(this);
    }
    x.stmtAST.accept(this);
  }

  public void visit(ReturnStmt x) {
    if (x.eAST instanceof EmptyExpr) {
      // ``return;'' requires void function return type:
      if (!currentFunctionReturnType.Tequal(StdEnvironment.voidType)) {
        reporter.reportError(errMsg[8], "", x.eAST.pos);
      }
      return; // done -> early exit
    }
    x.eAST.accept(this);
    if(x.eAST.type.AssignableTo(currentFunctionReturnType)) {
      if(currentFunctionReturnType.Tequal(StdEnvironment.floatType) &&
              x.eAST.type.Tequal(StdEnvironment.intType)) {
        x.eAST = i2f(x.eAST);
      }
    } else {
      reporter.reportError(errMsg[8], "", x.eAST.pos);
    }
  }

  public void visit(CompoundStmt x) {

    if (IsFunctionBlock) {
      IsFunctionBlock = false; // nested {...} need to open their own scope.
    } else {
      scopeStack.openScope();
    }
    x.astDecl.accept(this);
    scopeStack.closeScope();
  }

  public void visit(EmptyStmt x) {
  }

  public void visit(EmptyCompoundStmt x) {
  }

  public void visit(CallStmt x) {
    x.eAST.accept(this);
  }

  public void visit(VarDecl x) {
    if (x.tAST instanceof ArrayType) {
      ((ArrayType)x.tAST).astExpr.accept(this);
    }
    if (!(x.eAST instanceof EmptyExpr)) {
      x.eAST.accept(this);
      if (x.tAST instanceof ArrayType) {
        //Array declarations
        //errMst 13, 15, 16
        //perform i2f coercion if necessary
        if(!((ArrayType) x.tAST).astType.Tequal(StdEnvironment.errorType))
        {
          reporter.reportError(errMsg[15], "" , new SourcePos());
        }
        else if (((ArrayType) x.tAST).astType instanceof ArrayType && ((ArrayType) ((ArrayType) x.tAST).astType).equals(StdEnvironment.voidType))
        {
          reporter.reportError(errMsg[16], "", new SourcePos());
        }
        if(x.eAST.type.equals(StdEnvironment.floatType) && ((ArrayType) x.tAST).astType.equals(StdEnvironment.intType))
        {
          x.eAST.type = StdEnvironment.floatType;
        }
      } else {
        // Non-array declarations, i.e., scalar variables.
        // Check for error messages 14, 6.
        // Perform i2f coercion if necessary.
        if(x.eAST.type.equals(StdEnvironment.floatType) && x.tAST.equals(StdEnvironment.intType))
        {
          x.eAST.type = StdEnvironment.floatType;
        }
        if(x.eAST.type.equals(StdEnvironment.floatType) && x.tAST.equals(StdEnvironment.intType))
        {
          reporter.reportError(errMsg[14], "", new SourcePos());
        }
      }
    }
    // Here we are visiting a variable declaration x.
    // Enter this variable into the scope stack. Like with formal parameters,
    // if an identifier of the same name is already present, then you should
    // report Error 2.
    if (!scopeStack.enter(x.idAST.Lexeme, x))
    {
      reporter.reportError(errMsg[2], x.idAST.Lexeme, x.idAST.pos);
    }
    // Check that the variable is not of type void or void[].
    // Report error messages 3 and 4 respectively:
    if(x.tAST.Tequal(StdEnvironment.voidType))
    {
      if(x.tAST instanceof ArrayType)
      {
        reporter.reportError(errMsg[4], x.idAST.Lexeme, x.idAST.pos);
      }
      else {
        reporter.reportError(errMsg[3], x.idAST.Lexeme, x.idAST.pos);
      }
    }
    if (x.tAST instanceof ArrayType)
    {
      ((ArrayType) x.tAST).astExpr.accept(this);
    }
  }

  public void visit(DeclSequence x){
    x.D1.accept(this);
    x.D2.accept(this);
  }

  public void visit(VarExpr x) {
    x.Ident.accept(this);
    x.type = typeOfDecl (x.Ident.declAST);
    Decl varDecl = scopeStack.retrieve(x.Ident.Lexeme);

    if (varDecl == null)
    {
      reporter.reportError(errMsg[5], x.Ident.Lexeme, x.Ident.pos);
      x.type = StdEnvironment.errorType;
      return;
    }
    if(varDecl instanceof VarDecl || varDecl instanceof FormalParamDecl)
    {
      x.type = typeOfDecl(varDecl);
    }
    else{
      reporter.reportError(errMsg[11], x.Ident.Lexeme, x.Ident.pos);
      x.type = StdEnvironment.errorType;
    }
  }

  public void visit(AssignExpr x) {
    x.lAST.accept(this);
    x.rAST.accept(this);
    if(x.rAST.type.AssignableTo(x.lAST.type)) {
      //check for type coercion:
      if(x.lAST.type.Tequal(StdEnvironment.floatType) &&
              x.rAST.type.Tequal(StdEnvironment.intType)) {
        //coercion of right operand to int:
        x.rAST = i2f(x.rAST);
      }
    } else {
      reporter.reportError(errMsg[6], "", x.rAST.pos);
    }
    if(!(x.lAST instanceof VarExpr) && !(x.lAST instanceof ArrayExpr)) {
      reporter.reportError(errMsg[7], "", x.lAST.pos);
    }
  }

  public void visit(IntExpr x) {
    x.type = StdEnvironment.intType;
  }

  public void visit(FloatExpr x) {
    x.type = StdEnvironment.floatType;
  }

  public void visit(BoolExpr x) {
    x.type = StdEnvironment.boolType;
  }

  public void visit(StringExpr x) {
    x.type = StdEnvironment.stringType;
  }

  public void visit(ArrayExpr x) {
    x.idAST.accept(this);
    x.indexAST.accept(this);
    if(!x.indexAST.type.Tequal(StdEnvironment.intType)) {
      reporter.reportError(errMsg[17], "", x.indexAST.pos);
    }
    VarExpr VE = (VarExpr)x.idAST;
    if(!(typeOfDecl(VE.Ident.declAST) instanceof ArrayType)) {
      reporter.reportError(errMsg[12], "", x.pos);
      x.type = StdEnvironment.errorType;
    } else {
      x.type = typeOfArrayType(x.idAST.type);
    }
  }

  public void visit(BinaryExpr x) {
    x.lAST.accept(this);
    x.oAST.accept(this);
    x.rAST.accept(this);
    if(HasIntOrFloatArgs(x.oAST)) {
      if(x.lAST.type.Tequal(StdEnvironment.intType) &&
              x.rAST.type.Tequal(StdEnvironment.intType)) {
        x.oAST.type = StdEnvironment.intType;
        if(HasBoolReturnType(x.oAST)) {
          x.type = StdEnvironment.boolType;
        } else {
          x.type = StdEnvironment.intType;
        }
        return;
      } else if(x.lAST.type.Tequal(StdEnvironment.floatType) &&
              x.rAST.type.Tequal(StdEnvironment.floatType)) {
        x.oAST.type = StdEnvironment.floatType;
        if(HasBoolReturnType(x.oAST)) {
          x.type = StdEnvironment.boolType;
        } else {
          x.type = StdEnvironment.floatType;
        }
        return;
      } else if (x.lAST.type.Tequal(StdEnvironment.intType) &&
              x.rAST.type.Tequal(StdEnvironment.floatType)) {
        //coercion of left operand to float:
        x.lAST = i2f(x.lAST);
        x.oAST.type = StdEnvironment.floatType;
        if(HasBoolReturnType(x.oAST)) {
          x.type = StdEnvironment.boolType;
        } else {
          x.type = StdEnvironment.floatType;
        }
        return;
      } else if (x.lAST.type.Tequal(StdEnvironment.floatType) &&
              x.rAST.type.Tequal(StdEnvironment.intType)) {
        if((x.lAST.type.equals(StdEnvironment.floatType)) && (x.rAST.type.equals(StdEnvironment.intType)))
        {
          Operator op = new Operator("i2f", x.rAST.pos);
          //Type-cast the right operand to float
          x.rAST = new BinaryExpr(x.lAST, op, x.rAST, x.rAST.pos);
          x.rAST.type = StdEnvironment.floatType;
        }
        return;
      }
    }
    if (HasBoolArgs(x.oAST)) {
      if(x.lAST.type.Tequal(StdEnvironment.boolType) &&
              x.rAST.type.Tequal(StdEnvironment.boolType)) {
        x.oAST.type = StdEnvironment.intType;
        x.type = StdEnvironment.boolType;
        return;
      }
    }
    x.oAST.type = StdEnvironment.errorType;
    x.type = StdEnvironment.errorType;
    if (!((x.lAST.type instanceof ErrorType) || (x.rAST.type instanceof ErrorType)))
    {
      // Error not spurious, because AST children are ok.
      reporter.reportError(errMsg[9], "", x.pos);
    }
  }

  public void visit(UnaryExpr x) {
    x.oAST.accept(this);
    x.eAST.accept(this);
    switch (x.oAST.Lexeme)
    {
      case "!":
        if (!x.eAST.type.Tequal(StdEnvironment.boolType))
        {
          reporter.reportError(errMsg[10], "", x.oAST.pos);
        }
        x.type = StdEnvironment.boolType;
        break;
      case "-":
        if(!x.eAST.type.Tequal(StdEnvironment.intType) && !x.eAST.type.Tequal(StdEnvironment.floatType))
        {
          reporter.reportError(errMsg[10], "", x.oAST.pos);
        }
        x.type = x.eAST.type;
        break;
      default:
        assert false;
    }
  }

  public void visit(EmptyExpr x) {
  }

  public void visit(ActualParam x) {
    x.pAST.accept(this);
    x.type = x.pAST.type;
  }

  public void visit(EmptyActualParam x) {
  }

  public void visit(ActualParamSequence x) {
    x.lAST.accept(this);
    x.rAST.accept(this);
  }

  public void visit(CallExpr x) {
    //Here we perform semantic analysis of function calls:
    x.type = StdEnvironment.errorType;
    x.idAST.accept(this);
    x.paramAST.accept(this);
    //Retrieve the declaration of x from the scope stack:
    Decl D = scopeStack.retrieve(x.idAST.Lexeme);

    if (!(D instanceof FunDecl)) {
      reporter.reportError(errMsg[19], "", x.idAST.pos);
      return;
    }

    FunDecl F = (FunDecl ) D;
    // STEP 2:
    int NrFormalParams = GetNrOfFormalParams(F);
    int NrActualParams = GetNrOfActualParams(x);
    if (NrFormalParams != NrActualParams) {
      reporter.reportError(errMsg[20], "", x.idAST.pos);
      return;
    }
    //STEP1:
    for (int i = 1; i<= NrFormalParams; i++) {
      FormalParamDecl Form = GetFormalParam(F, i);
      ActualParam Act = GetActualParam(x, i);
      Type FormalT = Form.astType;
      Type ActualT = Act.pAST.type;
      if (!ActualT.Tequal(FormalT)) {
        reporter.reportError(errMsg[22], "", Act.pAST.pos);
      }
    }
    x.type = typeOfDecl(F);
  }

  public void visit(ExprSequence x) {
    x.lAST.accept(this);
    x.rAST.accept(this);
  }

  public void visit(ID x) {
    // STEP 1:
    // Here we look up the declaration of an identifier
    // from the scope stack. If no declaration can be found on the
    // scope stack, you should report Error 5.
    Decl binding = scopeStack.retrieve(x.Lexeme);
    if(binding != null) {
      x.declAST = binding;
    }
    if(binding == null)
      reporter.reportError(errMsg[5], x.Lexeme, x.pos);
    x.pos = new SourcePos();
  }

  public void visit(Operator x) {

  }

  public void visit(IntLiteral x) {

  }

  public void visit(FloatLiteral x) {

  }

  public void visit(BoolLiteral x) {

  }

  public void visit(StringLiteral x) {

  }

  public void visit(IntType x) {

  }

  public void visit(FloatType x) {

  }

  public void visit(BoolType x) {

  }

  public void visit(StringType x) {

  }

  public void visit(VoidType x) {

  }

  public void visit(ArrayType x) {

  }

  public void visit(ErrorType x) {

  }

}


