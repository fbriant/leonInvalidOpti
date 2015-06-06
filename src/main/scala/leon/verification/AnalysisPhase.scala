/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package verification

import purescala.Definitions._

import purescala.Expressions._
import purescala.ExprOps._
import leon.purescala.Types._
import leon.purescala.PrettyPrinter
import leon.purescala.Common._
import leon.verification.VCKinds._
import leon.evaluators._
import scala.concurrent.duration._
import leon.verification.IntOpti._

import solvers._

object AnalysisPhase extends LeonPhase[Program,VerificationReport] {
  val name = "Analysis"
  val description = "Leon Verification"

  implicit val debugSection = utils.DebugSectionVerification

  def run(ctx: LeonContext)(program: Program): VerificationReport = {
    val filterFuns: Option[Seq[String]] = ctx.findOption(SharedOptions.optFunctions)
    val timeout:    Option[Long]        = ctx.findOption(SharedOptions.optTimeout)

    val reporter = ctx.reporter

    // Solvers selection and validation
    val baseSolverF = SolverFactory.getFromSettings(ctx, program)

    val solverF = timeout match {
      case Some(sec) =>
        baseSolverF.withTimeout(sec.seconds)
      case None =>
        baseSolverF
    }

    val vctx = VerificationContext(ctx, program, solverF, reporter)
    
    reporter.debug("Generating Verification Conditions...")

    try { 
      val vcs = generateVCs(vctx, filterFuns)
      
      reporter.debug("Checking Verification Conditions...")
      checkVCs(vctx, vcs)
    } finally {
      solverF.shutdown()
    }
  }

  def generateVCs(vctx: VerificationContext, filterFuns: Option[Seq[String]]): Seq[VC] = {

    import vctx.reporter
    import vctx.program

    val defaultTactic   = new DefaultTactic(vctx)
    val inductionTactic = new InductionTactic(vctx)

    def excludeByDefault(fd: FunDef): Boolean = fd.annotations contains "library"

    val fdFilter = {
      import OptionsHelpers._

      filterInclusive(filterFuns.map(fdMatcher), Some(excludeByDefault _))
    }

    val toVerify = program.definedFunctions.filter(fdFilter).sortWith((fd1, fd2) => fd1.getPos < fd2.getPos)

    val vcs = for(funDef <- toVerify) yield {
      if (excludeByDefault(funDef)) {
        reporter.warning("Forcing verification of "+funDef.id.name+" which was assumed verified")
      }

      val tactic: Tactic =
        if(funDef.annotations.contains("induct")) {
          inductionTactic
        } else {
          defaultTactic
        }

      if(funDef.body.isDefined) {
        tactic.generateVCs(funDef)
      } else {
        Nil
      }
    }

    vcs.flatten
  }

  def checkVCs(
    vctx: VerificationContext,
    vcs: Seq[VC],
    checkInParallel: Boolean = false,
    stopAfter: Option[(VC, VCResult) => Boolean] = None
  ): VerificationReport = {
    val interruptManager = vctx.context.interruptManager

    var stop = false

    val initMap: Map[VC, Option[VCResult]] = vcs.map(v => v -> None).toMap

    val results = if (checkInParallel) {
      for (vc <- vcs.par if !stop) yield {
        val r = checkVC(vctx, vc)
        if (interruptManager.isInterrupted) interruptManager.recoverInterrupt()
        stop = stopAfter.exists(_(vc, r))
        vc -> Some(r)
      }
    } else {
      for (vc <- vcs.toSeq.sortWith((a,b) => a.fd.getPos < b.fd.getPos) if !interruptManager.isInterrupted && !stop) yield {
        val r = checkVC(vctx, vc)
        if (interruptManager.isInterrupted) interruptManager.recoverInterrupt()
        stop = stopAfter.exists(_(vc, r))
        vc -> Some(r)
      }
    }

    VerificationReport(initMap ++ results)
  }

  def checkVC(vctx: VerificationContext, vc: VC): VCResult = {
    import vctx.reporter
    import vctx.solverFactory

    val interruptManager = vctx.context.interruptManager

    val vcCond = vc.condition

    val s = solverFactory.getNewSolver()

    try {
      reporter.synchronized {
        reporter.info(s" - Now considering '${vc.kind}' VC for ${vc.fd.id} @${vc.getPos}...")
        reporter.debug(simplifyLets(vcCond).asString(vctx.context))
        reporter.debug("Solving with: " + s.name)
      }

      val tStart = System.currentTimeMillis

      s.assertCnstr(Not(vcCond))

      val satResult = s.check

      val dt = System.currentTimeMillis - tStart

      val res = satResult match {
        case _ if interruptManager.isInterrupted =>
          VCResult(VCStatus.Cancelled, Some(s), Some(dt))

        case None =>
          VCResult(VCStatus.Unknown, Some(s), Some(dt))

        case Some(false) =>
          VCResult(VCStatus.Valid, Some(s), Some(dt))

        case Some(true) => {
          /**
           * Try to approximate the invalid results when integers appears.s
           * Get as well the Verification context condition corresponding to these approximated results.
           */
          def getInvalidResultsOptimisation() : (Map[Identifier,Expr],Expr) = {
            /**
             * Computes absolute-minimal value of a list of integer.
             */
            /*def computeSign(list: List[Int], bigList: List[BigInt]) : (Int,Int) = {
              def computeBigSign() : Int = {
                val isBigPositive = bigList.filter(_ < 0).isEmpty
                val isBigNegative = bigList.filter(_ >= 0).isEmpty
                if (isBigPositive) {
                  1
                } else if (isBigNegative) {
                  -1
                } else {
                  0
                }
              }
              val bigIntSign = computeBigSign()
              val isOnlyPositive = list.filter(_ < 0).isEmpty
              val isOnlyNegative = list.filter(_ >= 0).isEmpty
              if (isOnlyPositive) {
                (1, bigIntSign)
              } else if (isOnlyNegative) {
                (-1, bigIntSign)
              } else {
                (0, bigIntSign)
              }
            }
            def computeMinimalValue(list: List[Int], bigList: List[BigInt], sign: Int, bigSign: Int) : (Int, BigInt) = {
              def computeBigIntMin() : BigInt = {
                if (!bigList.isEmpty && bigSign == 1) {
                  bigList.min
                } else if (!bigList.isEmpty && bigSign == -1) {
                  bigList.max
                } else {
                  0
                }
              }
              val bigIntMin = computeBigIntMin()
              if (!list.isEmpty && sign == 1) {
                (list.min, bigIntMin)
              } else if (!list.isEmpty && sign == -1) {
                (list.max, bigIntMin)
              } else {
                (0, bigIntMin)
              }
            }
            /**
             * Computes new invalid results by deducing the minimal value to all global Int variables.
             */
            def computeNewIntInvalidRes(invalidRes: Map[Identifier, Expr]) : Map[Identifier, Expr] = {
              def getUpdatedInt(invalidIntResId: List[(Identifier, Int)], invalidBigIntResId: List[(Identifier, BigInt)], intSign: Int, bigSign: Int) : (List[Int],List[BigInt]) = {
                def getRequirements() : (List[(Identifier, Int)], List[(Identifier, BigInt)]) = {
                  def getCompExpr(expr: Expr) : (List[(Identifier, Int)], List[(Identifier, BigInt)]) = expr match {
                    case GreaterThan(Variable(x),IntLiteral(i)) if intSign == 1  && i >= 0 => (List((x, i+1)),Nil)
                    case GreaterEquals(Variable(x),IntLiteral(i)) if intSign == 1 && i >= 0 => (List((x, i)),Nil)
                    case LessThan(Variable(x),IntLiteral(i)) if intSign == -1 && i < 0 => (List((x, i-1)),Nil)
                    case LessEquals(Variable(x),IntLiteral(i)) if intSign == -1 && i < 0 => (List((x, i)),Nil)
                    case GreaterThan(Variable(x),InfiniteIntegerLiteral(i)) if bigSign == 1  && i >= 0 => (Nil,List((x, i+1)))
                    case GreaterEquals(Variable(x),InfiniteIntegerLiteral(i)) if bigSign == 1 && i >= 0 => (Nil,List((x, i)))
                    case LessThan(Variable(x),InfiniteIntegerLiteral(i)) if bigSign == -1 && i < 0 => (Nil,List((x, i-1)))
                    case LessEquals(Variable(x),InfiniteIntegerLiteral(i)) if bigSign == -1 && i < 0 => (Nil,List((x, i)))
                    case And(exprs) => {
                      val resList = exprs.toList.map(getCompExpr(_))
                      (resList.flatMap(_._1), resList.flatMap(_._2))
                    }
                    case _ => (Nil,Nil)
                  }
                  vcCond match {
                    case Implies(lhs,rhs) => getCompExpr(lhs)
                    case _ => (Nil,Nil)
                  }
                }
                val (requirementInt,requirementBigInt) = getRequirements()
                val updatedIntInvalidRes = invalidIntResId.map(x => {
                  val filter = requirementInt.filter(_._1 == x._1)
                  if (filter.isEmpty) {
                    x._2
                  } else {
                    if (intSign == 1 ) {
                      x._2 - filter.map(_._2).max
                    } else {
                      x._2 + filter.map(_._2).min
                    }
                    
                  }
                })
                val updatedBigIntInvalidRes = invalidBigIntResId.map(x => {
                  val filter = requirementBigInt.filter(_._1 == x._1)
                  if (filter.isEmpty) {
                    x._2
                  } else {
                    if (bigSign == 1 ) {
                      x._2 - filter.map(_._2).max
                    } else {
                      x._2 + filter.map(_._2).min
                    }
                    
                  }
                })
                (updatedIntInvalidRes,updatedBigIntInvalidRes)
              }
              val invalidResSorted = invalidRes.toSeq.sortBy(_._1.name)
              val filterInvalidRes = invalidResSorted.filter(x => (x._2.isInstanceOf[IntLiteral]) || x._2.isInstanceOf[InfiniteIntegerLiteral])
              if (!filterInvalidRes.isEmpty) {
                def invalidIntFilteredRes(filter: List[(Identifier, Expr)]) : (List[(Identifier, Int)], List[(Identifier, BigInt)]) = filter match {
                  case (id, IntLiteral(i)) :: xs => {
                    val (nextIntFilter, nextBigIntFilter) = invalidIntFilteredRes(xs)
                    ((id, i) :: nextIntFilter, nextBigIntFilter)
                  }
                  case (id, InfiniteIntegerLiteral(i)) :: xs => {
                    val (nextIntFilter, nextBigIntFilter) = invalidIntFilteredRes(xs)
                    (nextIntFilter, (id, i) :: nextBigIntFilter)
                  }
                  case x :: xs => invalidIntFilteredRes(xs)
                  case Nil => (Nil,Nil)
                }
                val (invalidIntResId, invalidBigIntResId) = invalidIntFilteredRes(filterInvalidRes.toList)
                val (intSign, bigIntSign) = computeSign(invalidIntResId.map(_._2), invalidBigIntResId.map(_._2))
                val (updatedIntRes, updatedBigIntRes) = getUpdatedInt(invalidIntResId,invalidBigIntResId,intSign,bigIntSign)
                val (intMinimalValue,bigIntMinimalValue) = computeMinimalValue(updatedIntRes,updatedBigIntRes, intSign, bigIntSign)
                invalidRes.map(_ match {
                  case (id, v) if v.isInstanceOf[InfiniteIntegerLiteral] => (id, InfiniteIntegerLiteral(v.asInstanceOf[InfiniteIntegerLiteral].value - bigIntMinimalValue))
                  case (id, v) if v.isInstanceOf[IntLiteral] => (id, IntLiteral(v.asInstanceOf[IntLiteral].value - intMinimalValue))
                  case (id, v) => (id, v)
                })
              } else {
                invalidRes
              }
            }
            /**
             * Computes new invalid results by deducing locally minimal value inside a CaseClass.
             */
            def computeNewObjectInvalidRes(invalidRes: Map[Identifier, Expr]) : Map[Identifier, Expr] = {
              val invalidResSorted = invalidRes.toSeq.sortBy(_._1.name)
              if (invalidResSorted.exists(x => x._2.isInstanceOf[CaseClass])) {
                def intInside(obj: CaseClass) : List[Int] = {
                  def intInsideIter(list: Seq[Expr]) : List[Int] = list match {
                    case x :: xs if x.isInstanceOf[IntLiteral] => x.asInstanceOf[IntLiteral].value :: intInsideIter(xs)
                    case x :: xs if x.isInstanceOf[CaseClass] => intInside(x.asInstanceOf[CaseClass]) ::: intInsideIter(xs)
                    case x :: xs => intInsideIter(xs)
                    case Nil => Nil
                  }
                  intInsideIter(obj.args)
                }
                def changeIntInside(obj: CaseClass, min: Int) : CaseClass = {
                  def changeIntInsideIter(list: Seq[Expr]) : Seq[Expr] = list match {
                    case x :: xs if x.isInstanceOf[IntLiteral] => Seq(IntLiteral(x.asInstanceOf[IntLiteral].value - min)) ++ changeIntInsideIter(xs) 
                    case x :: xs if x.isInstanceOf[CaseClass] => Seq(changeIntInside(x.asInstanceOf[CaseClass],min)) ++ changeIntInsideIter(xs)
                    case x :: xs => changeIntInsideIter(xs)
                    case Nil => Nil
                  }
                  CaseClass(obj.ct, changeIntInsideIter(obj.args))
                }
                val invalidObjectRes: List[(Identifier,Expr)] = invalidResSorted.filter(x => x._2.isInstanceOf[CaseClass]).toList
                val invalidIntRes: List[(Identifier, List[Int])] = invalidObjectRes.map(x => (x._1, intInside((x._2.asInstanceOf[CaseClass])))).filter(x => !(x._2.isEmpty))
                val invalidMinRes: List[(Identifier, Int)] = invalidIntRes.map(x => (x._1, computeMinimalValue(x._2, Nil, computeSign(x._2, Nil)._1, 0)._1))
                invalidRes.map(_ match {
                  case (id, v) => {
                    val filter = invalidMinRes.filter(x => x._1 == id)
                    if (!(filter.isEmpty)) {
                      (id, changeIntInside(v.asInstanceOf[CaseClass],filter.head._2))
                    } else {
                      (id, v)
                    }
                  }
                })
              } else {
                invalidRes
              }
            }
            /**
             * Get the new Verification Context Condition corresponding to the approximated invalid results
             */
            def getNewVcCond(newInvalidRes: Map[Identifier, Expr], oldVcCond: Expr) : Expr = oldVcCond match {
              case Implies(lhs,rhs) => Implies(And(Seq(lhs) ++ newInvalidRes.toSeq.map(x => Equals(Variable(x._1),x._2))),rhs)
              case _ => Implies(And(newInvalidRes.toSeq.map(x => Equals(Variable(x._1),x._2))),oldVcCond)
            }*/
            val newIntRes = computeNewInvalidRes(s.getModel,vcCond)
            val newObjRes = computeNewObjectInvalidRes(newIntRes)
            (newObjRes, getNewVcCond(newObjRes,vcCond))
          }

          /**
           * Check which conjunctions of the post condition are violated by the counter-example.
           * Problem : Launch a verification for each conjunction
           */
          def getViolatedPostCond(invalidRes: Map[Identifier, Expr], vcCond: Expr) : List[Expr] = {
            /**
             * Calculates the list of Verification Context conditions with only a conjunction as a post-condition for all conjunctions of the original post condition.
             */
            def getNewPostConds() : List[(Expr,Expr)] = {
              /**
               * Removes the Implies linking Pre- and Post- conditions
               */
              def getOnlyPostCond(): Expr = vcCond match {
                case Implies(lhs, rhs) => rhs
                case _ => vcCond
              }
              /**
               * Removes the Let expression for post conditions that have multiple conjunction (it gives a value to "res").
               */
              def removeLet(cond: Expr) : (Expr, Option[Identifier], Option[Expr]) = cond match {
                case Let(id, value, body) => (body, Some(id), Some(value))
                case _ => (cond, None, None)
              }
              /**
               * Separates the conjunctions of the post condition
               */
              def separateConjunction(cond: Expr) : List[Expr] = cond match {
                case And(exprs) => exprs.toList.flatMap(separateConjunction(_))
                case _ => List(cond)
              }
              /**
               * Build a let with a separated conjunction for all conjunctions.
               */
              def buildLet(letId: Option[Identifier], letBody: Option[Expr], conds: List[Expr]) : List[Expr] = letId match {
                case Some(id) => conds.map(Let(id, letBody.get, _))
                case None => conds
              }
              val postCondExpr = getOnlyPostCond()
              val (postCond,letId, letBody) = removeLet(postCondExpr)
              val separatedConds = separateConjunction(postCond)
              buildLet(letId,letBody,separatedConds).zip(separatedConds)
            }
            /**
             * Launches a new verification with a particular Verification Context condition.
             * Returns true if the solver verified it.
             */
            def validateOneCond(cond: Expr, invalidRes: Map[Identifier, Expr]) : Boolean = {
              val eval = new CodeGenEvaluator(vctx.context, vctx.program)
              eval.eval(cond, invalidRes) match {
                case EvaluationResults.Successful(BooleanLiteral(b)) => b
                case _ => false
              }
            }
            val newPostConds = getNewPostConds()
            newPostConds.filter(x => !validateOneCond(x._1, invalidRes)).map(_._2)
          }
          def postCondCheck(newObjRes: Option[Map[Identifier,Expr]], violatedPostCond : Option[List[Expr]]) : VCResult = {
            vc.kind match {
              case Postcondition => VCResult(VCStatus.Invalid(s.getModel,newObjRes,violatedPostCond), Some(s), Some(dt))
              case _ => VCResult(VCStatus.Invalid(s.getModel,newObjRes,None), Some(s), Some(dt))
            }  
          }
          val violatedPostCond = getViolatedPostCond(s.getModel, vcCond)
          val (newObjRes, newVcCond) = getInvalidResultsOptimisation()
          if (!newObjRes.toSeq.zip(s.getModel.toSeq).filter(x => x._1._2 != x._2._2).isEmpty) {
            val newViolatedPostCond = getViolatedPostCond(newObjRes,newVcCond)
            if (violatedPostCond == newViolatedPostCond) {
              postCondCheck(Some(newObjRes),Some(violatedPostCond))
            } else {
              postCondCheck(None,Some(violatedPostCond))
            }
          } else {
            postCondCheck(None,Some(violatedPostCond))
          }


          
          // THINGS TO DO :
          // - What if mixed sign ?
          // - Can post cond be Implies ?
          // - BigInt ?
          // - postcond of RedBlackTree
        }  
      }

      reporter.synchronized {
        res.report(vctx)
      }

      res

    } finally {
      s.free()
    }
  }
}
