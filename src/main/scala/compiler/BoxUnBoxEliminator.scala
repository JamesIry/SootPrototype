package compiler

import soot._
import soot.toolkits.graph._
import soot.toolkits.scalar._
import soot.options._
import soot.jimple._
import soot.shimple._
import soot.shimple.toolkits.scalar._

import scala.collection.{ JavaConversions => JC }
import JC.collectionAsScalaIterable

import java.util.{ ArrayList, HashMap, Map, HashSet }

object BoxUnBoxEliminator extends BodyTransformer {

  override def internalTransform(b : Body, phaseName : String, options : Map[_, _]) {
    val body = b.asInstanceOf[ShimpleBody]
    val compiler = new Compiler
    val ctxt = new Context(body, compiler)

    if (Options.v().verbose())
      G.v().out.println("[" + body.getMethod().getName() +
        "] Eliminating unnecessary boxes and unboxes...");

    println("-- " + body.getMethod().getName() + " --")

    removeUnnecessaryAliases(body)

    val doUnsafe = false;
    if (doUnsafe) {
      copyUnboxesBeforePhi(body, ctxt)
    }
    copyBoxesAfterPhi(body, ctxt)

    removeUnnecessaryAliases(body)

    if (doUnsafe) {
//      copyUnboxesCloseToDef(body, ctxt)
    }
    copyBoxesCloseToUse(body, ctxt)

    val graph = new ExceptionalUnitGraph(body)
    val dominance = new MHGDominatorsFinder(graph)
        
    removedDupedUnboxes(body, dominance)

    
    removeUnnecessaryAliases(body)
    
    removeUnusedBoxes(body)
    removeUnnecessaryAliases(body)
    replaceUnboxesOfBoxes(body)
    replaceBoxesOfUnboxes(body)
    removeUnnecessaryAliases(body)
    removeUnusedBoxes(body)
    removeUnusedUnboxes(body)
    removeUnnecessaryAliases(body)

    removedDupedBoxes(body, dominance)
    
    removeUnnecessaryAliases(body)

  }

  def removedDupedBoxes(body : ShimpleBody, dominance : MHGDominatorsFinder[Unit]) {
    val stmts = body.getUnits
    val boxList = boxes(stmts).toList
    val dupedBoxes = new HashMap[AssignStmt, AssignStmt]
    for (dominated <- boxList) {
      val dominatedInvoke = dominated.getRightOp.asInstanceOf[StaticInvokeExpr]
      val dominatedUnboxed = (dominatedInvoke getArg 0).asInstanceOf[Immediate]
      for (dominator <- boxList) {
        if (dominated != dominator) {
          val dominatorInvoke = dominator.getRightOp.asInstanceOf[StaticInvokeExpr]
          val dominatorUnboxed = (dominatorInvoke getArg 0).asInstanceOf[Immediate]
          if ((dominatorUnboxed equivTo dominatedUnboxed) && (dominance isDominatedBy (dominated, dominator)) && dominator.getLeftOp.isInstanceOf[Local]) {
            val oldDominator = dupedBoxes get dominated
            if (oldDominator == null || (dominance isDominatedBy (oldDominator, dominator))) {
              dupedBoxes put (dominated, dominator)
            }
          }
        }
      }      
    }
    for (pair <- dupedBoxes.entrySet) {
      val dominated = pair.getKey
      val dominator = pair.getValue
      val dominatorTarget = dominator.getLeftOp
      val newUnit = Jimple.v newAssignStmt (dominated.getLeftOp(), dominatorTarget)
      stmts insertAfter (newUnit, dominated)
      stmts remove dominated
      println("Replaced duplicated box " + dominated.getLeftOp + " with " + dominatorTarget)
    }
    
  }

  def removedDupedUnboxes(body : ShimpleBody, dominance : MHGDominatorsFinder[Unit]) {
    val stmts = body.getUnits
    val unboxList = unboxes(stmts).toList
    val dupedUnboxes = new HashMap[AssignStmt, AssignStmt]
    for (dominated <- unboxList) {
      val dominatedInvoke = dominated.getRightOp.asInstanceOf[VirtualInvokeExpr]
      val dominatedBoxed = (dominatedInvoke.getBase).asInstanceOf[Immediate]
      for (dominator <- unboxList) {
        if (dominated != dominator) {
          val dominatorInvoke = dominator.getRightOp.asInstanceOf[VirtualInvokeExpr]
          val dominatorBoxed = (dominatorInvoke.getBase).asInstanceOf[Immediate]
          if ((dominatorBoxed equivTo dominatedBoxed) && (dominance isDominatedBy (dominated, dominator)) && dominator.getLeftOp.isInstanceOf[Local]) {
            val oldDominator = dupedUnboxes get dominated
            if (oldDominator == null || (dominance isDominatedBy (oldDominator, dominator))) {
              dupedUnboxes put (dominated, dominator)
            }
          }
        }
      }
    }
    
    for (pair <- dupedUnboxes.entrySet) {
      val dominated = pair.getKey
      val dominator = pair.getValue
      val dominatorTarget = dominator.getLeftOp
      val newUnit = Jimple.v newAssignStmt (dominated.getLeftOp(), dominatorTarget)
      stmts insertAfter (newUnit, dominated)
      stmts remove dominated
      println("Replaced duplicated unbox " + dominated.getLeftOp + " with " + dominatorTarget)
    }
  }

  final def getIndirectUsesOf(local : Local, uses : ShimpleLocalUses) : ArrayList[Unit] = {
    val directUses = getDirectUsesOf(local, uses)
    val indirectUses = new ArrayList[Unit](directUses.size)
    for (directUse <- directUses) {
      if (directUse.isInstanceOf[AssignStmt]) {
        val assign = directUse.asInstanceOf[AssignStmt]
        if (assign.getRightOp() == local && assign.getLeftOp.isInstanceOf[Local]) {
          val target = assign.getLeftOp.asInstanceOf[Local]
          indirectUses addAll getIndirectUsesOf(target, uses)
        } else {
          indirectUses add directUse
        }
      } else {
        indirectUses add directUse
      }
    }
    indirectUses
  }

  final def getDirectUsesOf(local : Local, uses : ShimpleLocalUses) : Iterable[Unit] = {
    (uses getUsesOf local).asInstanceOf[java.util.List[UnitValueBoxPair]] map (_.unit)
  }

  final def copyUnboxesCloseToDef(body : ShimpleBody, ctxt : Context) {
    var defs = new ShimpleLocalDefs(body)

    val stmts = body.getUnits

    for (assign <- unboxes(stmts).toList) {
      if (assign.getLeftOp.isInstanceOf[Local]) {
        val local = assign.getLeftOp.asInstanceOf[Local]
        val invoke = assign.getRightOp.asInstanceOf[VirtualInvokeExpr]
        if (invoke.getBase.isInstanceOf[Local]) {
          val base = invoke.getBase.asInstanceOf[Local]
          val directDefs = defs getDefsOf base
          for (defn <- directDefs) {
            // don't copy the unbox somewhere it already is
            if (stmts.getPredOf(defn) != assign) {
              val newLocal = ctxt unbox base
              val newUnit = stmts.getLast
              stmts.removeLast
              var target = defn
              var succ = stmts.getSuccOf(target)
              while (succ.isInstanceOf[IdentityStmt] && succ.asInstanceOf[IdentityStmt].getRightOp().isInstanceOf[ParameterRef]) {
                succ = stmts.getSuccOf(succ)
                target = stmts.getSuccOf(succ)
              }
              stmts insertAfter (newUnit, target)
              println("Copied unbox " + local + " closer to its definition, now " + newLocal)
            }
          }
        }
      }
    }
  }

  final def copyBoxesCloseToUse(body : ShimpleBody, ctxt : Context) {
    var uses = new ShimpleLocalUses(body)

    val stmts = body.getUnits

    for (assign <- boxes(stmts)) {
      if (assign.getLeftOp.isInstanceOf[Local]) {
        val local = assign.getLeftOp.asInstanceOf[Local]
        val invoke = assign.getRightOp.asInstanceOf[StaticInvokeExpr]
        val target = (invoke getArg 0).asInstanceOf[Immediate]
        val directUses = getDirectUsesOf(local, uses)
        for (use <- directUses) {
          // don't copy the box somewhere it already is
          if (stmts.getPredOf(use) != assign) {
            // don't copy a box before a phi, that's silly
            if (!(Shimple isPhiNode use)) {
              val newLocal = ctxt box target
              val newUnit = stmts.getLast
              stmts.removeLast
              newUnit addTag BoxTag
              stmts insertBefore (newUnit, use)

              use redirectJumpsToThisTo newUnit
              println("Copied box " + local + " closer to its use, now " + newLocal)
              for (box <- use.getUseBoxes) {
                if (local == box.getValue) {
                  box setValue newLocal
                }
              }
            }
          }
        }
      }
    }
  }

  final def copyBoxesAfterPhi(body : ShimpleBody, ctxt : Context) {
    val uses = new ShimpleLocalUses(body)
    val defs = new ShimpleLocalDefs(body)
    val stmts = body.getUnits
    for (box <- boxes(body.getUnits)) {
      if (box.getLeftOp.isInstanceOf[Local]) {
        val local = box.getLeftOp.asInstanceOf[Local]
        val directUses = getDirectUsesOf(local, uses)
        for (use <- directUses filter { x => Shimple isPhiNode x }) {
          val phiAssign = use.asInstanceOf[AssignStmt]
          val oldPhiTarget = phiAssign.getLeftOp

          val newPhiTarget = ctxt makeFreshLocal (ctxt.compiler getUnboxedType oldPhiTarget.getType)
          val newTemp = ctxt box newPhiTarget

          val newUnbox = stmts.getLast
          stmts remove newUnbox
          stmts insertAfter (newUnbox, phiAssign)
          stmts insertAfter (Jimple.v newAssignStmt (oldPhiTarget, newTemp), newUnbox)

          phiAssign setLeftOp newPhiTarget

          val phiExpr = Shimple getPhiExpr use
          val argCount = phiExpr.getArgCount

          val locals = new ArrayList[Value]
          val preds = new ArrayList[Unit]
          for (i <- 0 until argCount) {
            val phiPred = phiExpr getPred i
            val value = (phiExpr getValue i).asInstanceOf[Immediate]
            val newLocal = ctxt unbox value
            val newUnit = stmts.getLast
            stmts.removeLast

            val actualPred = if (phiPred.fallsThrough) {
              stmts insertAfter (newUnit, phiPred)
              newUnit
            } else {
              stmts insertBefore (newUnit, phiPred)
              phiPred
            }
            preds add actualPred
            locals add newLocal
          }
          phiAssign.setRightOp(Shimple.v newPhiExpr (locals, preds))
          println("copied box " + phiAssign.getLeftOp + " after phi " + oldPhiTarget)
          return copyBoxesAfterPhi(body, ctxt)
        }
      }
    }
  }

  final def copyUnboxesBeforePhi(body : ShimpleBody, ctxt : Context) {
    val defs = new ShimpleLocalDefs(body)

    val stmts = body.getUnits

    for (assign <- unboxes(stmts)) {
      val invoke = assign.getRightOp.asInstanceOf[VirtualInvokeExpr]
      if (invoke.getBase.isInstanceOf[Local]) {
        val boxed = invoke.getBase.asInstanceOf[Local]
        val boxDefs = defs getDefsOf boxed

        if (boxDefs.size == 1 && (Shimple isPhiNode (boxDefs get 0))) {
          val phiAssign = (boxDefs get 0).asInstanceOf[AssignStmt]
          val phiExpr = Shimple getPhiExpr phiAssign
          val oldPhiTarget = Shimple getLhsLocal phiAssign

          val newPhiTarget = ctxt makeFreshLocal (ctxt.compiler getUnboxedType oldPhiTarget.getType)
          val newTemp = ctxt box newPhiTarget

          val newBox = stmts.getLast
          stmts remove newBox
          stmts insertAfter (newBox, phiAssign)
          stmts insertAfter (Jimple.v newAssignStmt (oldPhiTarget, newTemp), newBox)

          phiAssign setLeftOp newPhiTarget

          val count = phiExpr.getArgCount
          val locals = new ArrayList[Value]
          val preds = new ArrayList[Unit]
          for (i <- 0 until count) {
            val pred = phiExpr getPred i
            val toUnbox = phiExpr getValue i

            val newLocal = ctxt unbox toUnbox
            val newPred = stmts.getLast
            stmts remove newPred
            val actualPred = if (pred.fallsThrough) {
              stmts insertAfter (newPred, pred)
              newPred
            } else {
              stmts insertBefore (newPred, pred)
              pred redirectJumpsToThisTo newPred
              pred
            }

            locals add newLocal
            preds add actualPred
          }
          phiAssign.setRightOp(Shimple.v newPhiExpr (locals, preds))
          println("copied unbox " + assign.getLeftOp + " before a phi " + oldPhiTarget)
          return copyUnboxesBeforePhi(body, ctxt)
        }
      }
    }
  }
  def isBox(unit : Unit) = unit.getTags contains BoxTag
  def isUnbox(unit : Unit) = unit.getTags contains UnboxTag

  def removeUnnecessaryAliases(body : ShimpleBody) {
    val uses = new ShimpleLocalUses(body)
    val locals = body.getLocals
    val removedStatements = new ArrayList[Unit]

    def removeUnnecessaryAliases(local : Local, orig : Local) {
      val directUses = getDirectUsesOf(local, uses)
      for (directUse <- directUses) {
        if (directUse.isInstanceOf[AssignStmt]) {
          val assign = directUse.asInstanceOf[AssignStmt]
          if (assign.getRightOp() == local && assign.getLeftOp.isInstanceOf[Local]) {
            val alias = assign.getLeftOp.asInstanceOf[Local]
            removeUnnecessaryAliases(alias, orig)
            println("Replaced unnnecessary alias " + alias + " with " + orig)
            removedStatements add assign
          }
        }
        for (box <- directUse.getUseBoxes) {
          if (box.getValue == local) {
            box setValue orig
          }
        }
      }
    }

    for (local <- locals) {
      removeUnnecessaryAliases(local, local)
    }
    for (unit <- removedStatements) {
      removeUnit(body, unit)
    }
  }

  def boxes(stmts : Iterable[Unit]) : Iterable[AssignStmt] = {
    (stmts filter isBox).asInstanceOf[Iterable[AssignStmt]]
  }

  def unboxes(stmts : Iterable[Unit]) : Iterable[AssignStmt] = {
    (stmts filter isUnbox).asInstanceOf[Iterable[AssignStmt]]
  }

  def removeUnusedBoxes(body : ShimpleBody) {
    val uses = new ShimpleLocalUses(body)
    val removedBoxes = new java.util.ArrayList[Unit]

    for (assign <- boxes(body.getUnits)) {
      val target = assign.getLeftOp.asInstanceOf[Local]
      val invoke = assign.getRightOp.asInstanceOf[StaticInvokeExpr]
      val targetUses = getDirectUsesOf(target, uses)
      if (targetUses.size == 0) {
        println("Removed box " + target + " that is not used")
        removedBoxes add assign
      }
    }

    for (unit <- removedBoxes) {
      removeUnit(body, unit)
    }
  }

  def removeUnusedUnboxes(body : ShimpleBody) {
    val uses = new ShimpleLocalUses(body)
    for (assign <- unboxes(body.getUnits)) {
      if (assign.getLeftOp.isInstanceOf[Local]) {
        val target = assign.getLeftOp.asInstanceOf[Local]
        val targetUses = getDirectUsesOf(target, uses)
        if (targetUses.size == 0) {
          println("Found unbox " + target + " is not used but not doing anything about it - should replace it with a null check")
          //                nullChecks add stmt        
        }
      }
    }
  }

  def replaceUnboxesOfBoxes(body : ShimpleBody) {
    val uses = new ShimpleLocalUses(body)
    for (assign <- boxes(body.getUnits)) {
      if (assign.getLeftOp.isInstanceOf[Local]) {
        val target = assign.getLeftOp.asInstanceOf[Local]
        val invoke = assign.getRightOp.asInstanceOf[StaticInvokeExpr]
        val unBoxed = (invoke getArg 0).asInstanceOf[Immediate]
        val targetUses = getDirectUsesOf(target, uses)
        for (unbox <- unboxes(targetUses)) {
          unbox setRightOp unBoxed
          unbox.getTags remove UnboxTag
          println("Replaced unbox " + unbox.getLeftOp + " with its orignal unboxed value")
        }
      }
    }
  }

  def replaceBoxesOfUnboxes(body : ShimpleBody) {
    val uses = new ShimpleLocalUses(body)
    for (assign <- unboxes(body.getUnits)) {
      if (assign.getLeftOp.isInstanceOf[Local]) {
        val target = assign.getLeftOp.asInstanceOf[Local]
        val invoke = assign.getRightOp.asInstanceOf[VirtualInvokeExpr]
        val boxed = invoke.getBase
        val targetUses = getDirectUsesOf(target, uses)
        for (box <- boxes(targetUses)) {
          box setRightOp boxed
          box.getTags remove BoxTag
          println("Replaced box " + box.getLeftOp + " with it original boxed value")
        }
      }
    }
  }

  def removeUnit(body : ShimpleBody, unit : Unit) {    
  // this shouldn't have to exist update of references shouldn't have to exist
    val succ = body.getUnits() getSuccOf unit
    val pred = body.getUnits() getPredOf unit
    for (box <- unit.getBoxesPointingToThis().toList) {
      if (box.isBranchTarget()) {
        box setUnit succ
      } else {
        box setUnit pred
      }
    }

    // end of stuff that shouldn't have to exist
    body.getUnits remove unit

    if (unit.isInstanceOf[AssignStmt]) {
      val assign = unit.asInstanceOf[AssignStmt]
      if (assign.getLeftOp.isInstanceOf[Local]) {
        val local = assign.getLeftOp.asInstanceOf[Local]
        body.getLocals remove local
      }
    }
  }
}