package compiler

import soot._

object Test extends App {
/*
// Apex-ish
public class Test {
    Integer result;
    if (x > y) {
      result = x - y;
    } else {
      result = y - x;
    }
    return result;
}

// Java-ish
public class Test {
    public Integer test(Integer x, Integer y) {
       Integer result;
       if (Boolean.valueOf(x.intValue() > y.intValue()).booleanValue()) {
          result = Integer.valueOf(x.intValue() - y.intValue());
       } else {
          result = Integer.valueOf(y.intValue() - x.intValue());
       }
       return result;
    }
}
*/
  
  
    val clazz = new ClassDef("Test")(
     new MethodDef("test1", IntTy(), FormalParam("x", IntTy()), FormalParam("y", IntTy())) (
        VrblDefStmt("result", IntTy()),  
        If(Gt(VrblExpr("x", IntTy()), VrblExpr("y", IntTy())), 
            AssgnStmt("result", Subtract(VrblExpr("x", IntTy()), VrblExpr("y", IntTy()))),
            AssgnStmt("result", Subtract(VrblExpr("y", IntTy()), VrblExpr("x", IntTy())))),
        RetStmt(VrblExpr("result", IntTy()))
      ),
      new MethodDef("test2", IntTy(), FormalParam("x", IntTy()), FormalParam("y", IntTy())) (
        While(Gt(VrblExpr("x", IntTy()), IntExpr(0)), 
            AssgnStmt("x", Subtract(VrblExpr("x", IntTy()), VrblExpr("y", IntTy())))),
        RetStmt(VrblExpr("x", IntTy()))
      ),
      new MethodDef("test3", VoidTy()) (
        VrblDefStmt("x", IntTy()),
        AssgnStmt("x", IntExpr(10)),
        While(Gt(VrblExpr("x", IntTy()), IntExpr(0)), 
            AssgnStmt("x", Subtract(VrblExpr("x", IntTy()), IntExpr(1)))),
        RetStmt(Void)
      )      
    )

  G.reset
  Scene.v loadClassAndSupport Compiler.OBJECT
  Scene.v loadClassAndSupport Compiler.INTEGER
  Scene.v loadClassAndSupport Compiler.BOOLEAN
    
    val c = new Compiler
    c compile clazz
}