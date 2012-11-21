package compiler

sealed abstract class Ty
case class IntTy() extends Ty
case class BoolTy() extends Ty
case class VoidTy() extends Ty

sealed abstract class Stmt
case class VrblDefStmt[T <: Ty](name : String, ty : T) extends Stmt
case class AssgnStmt[T <: Ty](name : String, expr : Expr[T]) extends Stmt
case class If(cond : Expr[BoolTy], stmt1 : Stmt, Stm2 : Stmt) extends Stmt
case class RetStmt[T <: Ty](expr : Expr[T]) extends Stmt
case class While(cond : Expr[BoolTy], stmt : Stmt) extends Stmt

sealed abstract class Expr[T <: Ty]
case class Subtract(l : Expr[IntTy], r : Expr[IntTy]) extends Expr[IntTy]
case class Add(l : Expr[IntTy], r : Expr[IntTy]) extends Expr[IntTy]
case class IntExpr(n : Int) extends Expr[IntTy]
case class BoolExpr(b : Boolean) extends Expr[BoolTy]
case class NullExpr[T <: Ty]() extends Expr[T]
case object Void extends Expr[VoidTy]
case class VrblExpr[T <: Ty](name : String, ty : T) extends Expr[T]
case class Gt(l : Expr[IntTy], r : Expr[IntTy]) extends Expr[BoolTy]

case class FormalParam(name : String, ty : Ty)

class MethodDef(val name : String, val returnType : Ty, val params : FormalParam*)(val stmts : Stmt*)

class ClassDef(val name : String)(val methods : MethodDef*)