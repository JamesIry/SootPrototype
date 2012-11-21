import soot._
import soot.jimple._
import soot.baf._
import soot.options._
import soot.util._

import java.io._

import java.util.Arrays

import scala.collection.JavaConversions

object BoxMath extends App {
  import JavaConversions.collectionAsScalaIterable
  
  val OBJECT = "java.lang.Object"
  val INTEGER = "java.lang.Integer"

  Scene.v loadClassAndSupport OBJECT
  Scene.v loadClassAndSupport INTEGER

  val sClass = new SootClass("BoxMath", Modifier.PUBLIC)
  sClass setSuperclass (Scene.v getSootClass OBJECT)
  Scene.v addClass sClass
  
  val method = new SootMethod("add", Arrays asList (RefType v INTEGER, RefType v INTEGER), RefType v INTEGER, Modifier.PUBLIC)
  sClass addMethod method

  val body = Jimple.v newBody method
  method setActiveBody body
  
  val locals = body.getLocals
  val units = body.getUnits

  val x = Jimple.v newLocal("x", RefType v INTEGER)
  locals add x
  units add Jimple.v.newIdentityStmt(x, Jimple.v newParameterRef (RefType v INTEGER, 0))

  val y = Jimple.v newLocal("y", RefType v INTEGER)
  locals add y
  units add Jimple.v.newIdentityStmt(y, Jimple.v newParameterRef (RefType v INTEGER, 1))
  
  val unboxIntRef = (Scene.v getMethod "<" + INTEGER + ": int intValue()>").makeRef
  val boxIntRef = (Scene.v getMethod "<" + INTEGER + ": " + INTEGER + " valueOf(int)>").makeRef

  def unboxInt(x : Local) = Jimple.v newVirtualInvokeExpr(x, unboxIntRef)
  def boxInt(x : Local) = Jimple.v newStaticInvokeExpr(boxIntRef, Arrays asList x)
  
  val xUnbox = Jimple.v newLocal("xUnbox", IntType.v)
  locals add xUnbox
  units add Jimple.v.newAssignStmt(xUnbox, unboxInt(x))
  
  val yUnbox = Jimple.v newLocal("yUnbox", IntType.v)
  locals add yUnbox
  units add Jimple.v.newAssignStmt(yUnbox, unboxInt(y))
  
  val zUnbox = Jimple.v newLocal("zUnbox", IntType.v)
  locals add zUnbox
  units add Jimple.v.newAssignStmt(zUnbox, Jimple.v newAddExpr (xUnbox, yUnbox))
  
  val z = Jimple.v newLocal("z", RefType v INTEGER)
  locals add z
  units add Jimple.v.newAssignStmt(z, boxInt(zUnbox))
  
  units.add (Jimple.v newRetStmt z)
  
  for (clazz <- List(sClass)) {
      dumpClass(clazz, new soot.jimple.JasminClass(_))
      optimize(clazz)
      dumpClass(clazz, new soot.baf.JasminClass(_))
  }
  
  def optimize(sClass : SootClass) =
    for (method <- sClass.getMethods) {
      if (method.hasActiveBody) {
        val body = method.getActiveBody
        val bafBody = Baf.v newBody body
        method setActiveBody bafBody
      }
    }
  
  def dumpClass(sClass : SootClass, f : SootClass => AbstractJasminClass) {      
      val out1 = new PrintWriter(System.out)  
      
      val fileName = SourceLocator.v.getFileNameFor(sClass, Options.output_format_class)
      out1 println (fileName + "\n")
      out1.flush
      
      val jasminClass = f(sClass)
      Printer.v printTo (sClass, out1)
      jasminClass print out1
      out1.flush    
/*  
  val out2 = new PrintWriter(new OutputStreamWriter(new JasminOutputStream(new FileOutputStream(fileName))))
  
  try {
      
      jasminClass.print(out2)
      out2.flush
  } finally {
    out2.close
  } */
  }
  
}