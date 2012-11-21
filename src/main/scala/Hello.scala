import soot._
import soot.jimple._
import soot.baf._
import soot.options._
import soot.util._

import java.io._

import java.util.Arrays

import scala.collection.JavaConversions

object Hello extends App {
  import JavaConversions.collectionAsScalaIterable
  
  val OBJECT = "java.lang.Object"
  val SYSTEM = "java.lang.System"
  val STRING = "java.lang.String"
  val PRINTSTREAM = "java.io.PrintStream"
    
  Scene.v addClass (new SootClass(OBJECT, Modifier.PUBLIC))
  
  val printStreamClass = new SootClass(PRINTSTREAM, Modifier.PUBLIC)
  printStreamClass addMethod (new SootMethod("println", Arrays asList (RefType v STRING), VoidType.v, Modifier.PUBLIC))
  Scene.v addClass printStreamClass
  
  val systemClass = new SootClass(SYSTEM, Modifier.PUBLIC)
  systemClass addField (new SootField("out", RefType v PRINTSTREAM, Modifier.PUBLIC | Modifier.STATIC))  
  Scene.v addClass systemClass
  
  val sClass = new SootClass("HelloWorld", Modifier.PUBLIC)
  sClass setSuperclass (Scene.v getSootClass OBJECT)
  Scene.v addClass sClass
  
  val argTypes = Arrays asList (ArrayType v (RefType v STRING, 1))
  val method = new SootMethod("main", argTypes, VoidType.v, Modifier.PUBLIC | Modifier.STATIC)
  sClass addMethod method
  
  val body = Jimple.v newBody method
  method setActiveBody body
  
  val locals = body.getLocals
  val units = body.getUnits
  
  val argList = Jimple.v.newLocal("argList", ArrayType.v(RefType v STRING, 1))
  locals add argList
  units add Jimple.v.newIdentityStmt(argList, Jimple.v.newParameterRef(ArrayType.v(RefType.v(STRING), 1), 0))
  
  val outRef = Jimple.v.newLocal("tmpRef", RefType v PRINTSTREAM)
  locals add outRef
  units add (Jimple.v.newAssignStmt(outRef, Jimple.v.newStaticFieldRef(Scene.v.getField("<" + SYSTEM + ": " + PRINTSTREAM + " out>").makeRef)))
  
  val toCall = Scene.v getMethod "<" + PRINTSTREAM + ": void println(" + STRING + ")>"
  units add Jimple.v.newInvokeStmt(Jimple.v.newVirtualInvokeExpr(outRef, toCall.makeRef, StringConstant.v("Hello moose")))
  
  units add Jimple.v.newReturnVoidStmt    
  
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