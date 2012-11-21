package compiler

import soot._
import soot.util.Chain
import jimple._

import java.io._

import java.util.Arrays

import scala.collection.mutable.HashMap

import soot.baf._
import soot.shimple._
import soot.options._
import soot.jimple.toolkits.scalar.CommonSubexpressionEliminator
import soot.tagkit.Tag

import scala.collection.{ JavaConversions => JC }
import JC.collectionAsScalaIterable

class Context(body : Body, val compiler : Compiler) {
  val BoxedIntTy = compiler.BoxedIntTy
  val BoxedBoolTy = compiler.BoxedBoolTy
  
  val UnboxedIntTy = compiler.UnboxedIntTy
  val UnboxedBoolTy = compiler.UnboxedBoolTy
  
  private val localsMap = HashMap[String, Local]()
  
  for (local <- body.getLocals()) {
    localsMap put (local.getName, local)
  }
  def getLocal(name : String) = (localsMap get name).get
  def addLocal(local : Local) = {
    body.getLocals add local
    localsMap put (local.getName, local)
  }
  
  def makeLocal(name : String, sType : Type) = {
    val local = Jimple.v newLocal (name, sType)
    this addLocal local
    local
  }
  
  def makeFreshLocal(sType : Type) = {
    val fresh = (body getTag "FreshTag").asInstanceOf[FreshTag]
    fresh.value += 1
    this makeLocal ("$t" + (fresh.value - 1), sType)    
  }
  
  def addUnit(unit : Unit) = {
    body.getUnits add unit
    unit
  }
  
  def assignFresh(value : Value, tag : Option[Tag]) = {
    val ty = value.getType()
    val local = if (ty == VoidType.v) null else this makeFreshLocal ty
    val unit = if (ty == VoidType.v) Jimple.v newInvokeStmt value else Jimple.v newAssignStmt (local, value)
    for (tag_ <- tag) unit addTag tag_
    this addUnit unit
    local
  }
  
  def virtualInvoke(target : Local, method : SootMethodRef, tag : Option[Tag], args : Immediate*) =
    this assignFresh (Jimple.v newVirtualInvokeExpr (target, method, JC.seqAsJavaList(args)), tag)
  
  def staticInvoke(method : SootMethodRef, tag : Option[Tag], args : Immediate*) =
    this assignFresh (Jimple.v newStaticInvokeExpr (method, JC.seqAsJavaList(args)), tag)
  
  
  def unbox(x : Value) = {
    val local = x match {
      case y : Local => y
      case _ => assignFresh(x, None) 
    }
    val ty = local.getType()
    val unboxer = ty match {
      case BoxedIntTy => compiler.unboxIntRef
      case BoxedBoolTy => compiler.unboxBoolRef
    }
    this virtualInvoke (local, unboxer, Some(UnboxTag))
  }
  
  def box(x : Immediate) = {
    val ty = x.getType()
    val boxer = ty match {
      case UnboxedIntTy => compiler.boxIntRef
      case UnboxedBoolTy => compiler.boxBoolRef
    }
    this staticInvoke (boxer, Some(BoxTag), x)
  }  
  
  def makeParamRef(name : String, ty : Type, idx : Int) = {
    val local = this makeLocal (name, ty)
    this addUnit (Jimple.v newIdentityStmt (local, Jimple.v newParameterRef (ty, idx)))
    local
  }
}

object Compiler {
  val OBJECT = "java.lang.Object"
  val INTEGER = "java.lang.Integer"
  val BOOLEAN = "java.lang.Boolean"  
}
class Compiler {
  val BoxedIntTy = RefType v Compiler.INTEGER
  val BoxedBoolTy = RefType v Compiler.BOOLEAN
  
  val UnboxedIntTy = IntType.v
  val UnboxedBoolTy = BooleanType.v
  
  
  import Compiler._

  val unboxIntRef = (Scene.v getMethod "<" + INTEGER + ": int intValue()>").makeRef
  val boxIntRef = (Scene.v getMethod "<" + INTEGER + ": " + INTEGER + " valueOf(int)>").makeRef

  val unboxBoolRef = (Scene.v getMethod "<" + BOOLEAN + ": boolean booleanValue()>").makeRef
  val boxBoolRef = (Scene.v getMethod "<" + BOOLEAN + ": " + BOOLEAN + " valueOf(boolean)>").makeRef

  def sootTy(ty : Ty) = ty match {
    case BoolTy() => BoxedBoolTy
    case IntTy() => BoxedIntTy
    case VoidTy() => VoidType.v
  }
  
  def getUnboxedType(ty : Type) = ty match {
    case BoxedBoolTy => UnboxedBoolTy
    case BoxedIntTy => UnboxedIntTy
  }

  def getBoxedType(ty : Type) = ty match {
    case UnboxedBoolTy => BoxedBoolTy
    case UnboxedIntTy => BoxedIntTy
  }

  def True = IntConstant v 1
  def False = IntConstant v 0
  def getBoolean(b : Boolean) = if (b) True else False
  
  def compileExpr[T <: Ty](ctxt : Context, expr : Expr[T]) : Immediate = expr match {
    case Subtract(l, r) =>
      ctxt box(ctxt assignFresh(Jimple.v newSubExpr (ctxt unbox(this compileExpr (ctxt, l)), ctxt unbox(this compileExpr (ctxt, r))), None))
    case Add(l, r) =>
      ctxt box(ctxt assignFresh(Jimple.v newAddExpr (ctxt unbox(this compileExpr (ctxt, l)), ctxt unbox(this compileExpr (ctxt, r))), None))
    case IntExpr(value) => ctxt box(IntConstant v value)
    case BoolExpr(value) => ctxt box(this getBoolean value)
    case NullExpr() => NullConstant.v
    case Void => null
    case VrblExpr(name, _) => ctxt getLocal name
    case Gt(l, r) => {
      val result = ctxt makeFreshLocal BooleanType.v
      val trueTarget = Jimple.v newAssignStmt (result, IntConstant v 0)
      ctxt addUnit (Jimple.v newIfStmt (Jimple.v newLeExpr (ctxt unbox(this compileExpr (ctxt, r)), ctxt unbox(this compileExpr (ctxt, l))), trueTarget))
      ctxt addUnit (Jimple.v newAssignStmt (result, IntConstant v 1))
      val endIf = Jimple.v.newNopStmt
      ctxt addUnit (Jimple.v newGotoStmt endIf)
      ctxt addUnit trueTarget
      ctxt addUnit endIf
      ctxt box result
    }
  }

  def compileStmt(ctxt : Context, stmt : Stmt) : Unit = stmt match {
    case VrblDefStmt(name, ty) => {
      ctxt makeLocal (name, this sootTy ty)
      null
    }
    case AssgnStmt(name, expr) => {
      ctxt addUnit (Jimple.v newAssignStmt (ctxt getLocal name, this compileExpr (ctxt, expr)))
    }
    case RetStmt(expr) => {
      val result = this compileExpr (ctxt, expr)
      if (expr == Void) {
        ctxt addUnit Jimple.v.newReturnVoidStmt
      } else {
        ctxt addUnit (Jimple.v newReturnStmt result)
      }
    }
    case If(cond, stmt1, stmt2) => {
      val condLocal = ctxt unbox (this compileExpr (ctxt, cond))
      val trueTarget = Jimple.v.newNopStmt
      ctxt addUnit (Jimple.v newIfStmt (Jimple.v newNeExpr (condLocal, IntConstant v 0), trueTarget))
      this compileStmt (ctxt, stmt2)
      val endIfJump = Jimple.v.newNopStmt
      ctxt addUnit (Jimple.v newGotoStmt (endIfJump))
      ctxt addUnit trueTarget
      this compileStmt (ctxt, stmt1)
      ctxt addUnit endIfJump
    }
    case While(cond, stmt) => {
      val topOfLoop = Jimple.v.newNopStmt
      val exitLoop = Jimple.v.newNopStmt
      ctxt addUnit topOfLoop
      val condLocal = ctxt unbox (this compileExpr (ctxt, cond))
      ctxt addUnit (Jimple.v newIfStmt (Jimple.v newEqExpr (condLocal, IntConstant v 0), exitLoop))
      this compileStmt (ctxt, stmt)
      ctxt addUnit (Jimple.v newGotoStmt (topOfLoop))
      ctxt addUnit exitLoop
    }
  }  

  def compileClass(clazz : ClassDef) : SootClass = {
    val sClass = new SootClass(clazz.name, Modifier.PUBLIC)
    sClass setSuperclass (Scene.v getSootClass OBJECT)
    Scene.v addClass sClass

    for (method <- clazz.methods) {
      val sMethod = new SootMethod(method.name, JC.seqAsJavaList(method.params map { case FormalParam(_, ty) => sootTy(ty) }), sootTy(method.returnType), Modifier.PUBLIC)
      sClass addMethod sMethod

      val body = Jimple.v newBody sMethod
      body addTag (new FreshTag)
      sMethod setActiveBody body
      
      val ctxt = new Context(body, this)

      for ((param, idx) <- method.params.zipWithIndex) {
        ctxt makeParamRef(param.name, sootTy(param.ty), idx)
      }

      for (stmt <- method.stmts) {
        this compileStmt (ctxt, stmt)
      }
    }
    sClass
  }

  def compile(classes : ClassDef*) : Seq[SootClass] = {
    val sClasses = classes map compileClass

    // this disables all the automatic optimizations applied in the conversion from jimple to baf
    /*      
  val it = (PackManager.v getPack "bb").iterator()
  val myBB = new BodyPack("bb")
  while (it.hasNext()) {
    val transform = it.next().asInstanceOf[Transform]
    myBB add transform
    it.remove()
  } */

    PhaseOptions.v.setPhaseOption("bb.lso", "inter:true")

    for (clazz <- sClasses) {
//      dumpClass(clazz, "original jimple")
      optimizeTransformer(clazz, soot.jimple.toolkits.scalar.NopEliminator.v, "nopEliminator", false)

      convertBody(clazz, { b => Shimple.v newBody b }, "shimple", false)
      optimizePack(clazz, PackManager.v getPack "shimple", "shimple opt", true)
      optimizeTransformer(clazz, BoxUnBoxEliminator, "boxunbox elim", true)

      convertBody(clazz, { b => b.asInstanceOf[ShimpleBody].toJimpleBody() }, "back to jimple", false)
      optimizePack(clazz, PackManager.v getPack "jb", "jb", false)
      optimizePack(clazz, PackManager.v getPack "jop", "jop", false)

      convertBody(clazz, { b => Baf.v newBody b }, "baf", false)
      optimizePack(clazz, PackManager.v getPack "bb", "bb", true)
    }

    def convertBody(clazz : SootClass, f : Body => Body, name : String, dump : Boolean) {
      for (method <- clazz.getMethods) {
        if (method.hasActiveBody) {
          val body = method.getActiveBody
          val newBody = f(body)
          newBody addAllTagsOf body
          method setActiveBody newBody 
        }
      }
      if (dump)
        dumpClass(clazz, name)
    }

    def optimizePack(clazz : SootClass, pack : Pack, name : String, dump : Boolean) {
      for (method <- clazz.getMethods) {
        if (method.hasActiveBody) {
          val body = method.getActiveBody
          pack apply body
        }
      }
      if (dump)
        dumpClass(clazz, name)
    }

    def optimizeTransformer(clazz : SootClass, transformer : BodyTransformer, name : String, dump : Boolean) {
      for (method <- clazz.getMethods) {
        if (method.hasActiveBody) {
          val body = method.getActiveBody
          transformer transform body
        }
      }
      if (dump)
        dumpClass(clazz, name)
    }

    def dumpClass(sClass : SootClass, name : String) {
      val out1 = new PrintWriter(System.out)

      val fileName = SourceLocator.v.getFileNameFor(sClass, Options.output_format_class)
      out1 println (fileName + " " + name + "\n")
      out1.flush

      Printer.v printTo (sClass, out1)
      out1.flush

      try {
        val jasminClass = if (sClass.containsBafBody) new baf.JasminClass(sClass) else new jimple.JasminClass(sClass)
        jasminClass print out1
        out1.flush
      } catch {
        case e : RuntimeException => println("could not dump jasmine class")
      }
      /*  
  val out2 = new PrintWriter(new OutputStreamWriter(new JasminOutputStream(new FileOutputStream(fileName))))
  
  try {
      
      jasminClass.print(out2)
      out2.flush
  } finally {
    out2.close
  } */

      println("-------------------- end " + name + "---------------------")
    }

    sClasses
  }
}