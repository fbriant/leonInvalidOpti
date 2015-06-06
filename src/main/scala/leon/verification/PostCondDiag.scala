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

import solvers._

object PostCondDiag {
  
  /**
   * Removes the Implies linking Pre- and Post- conditions
   */
  private def getOnlyPostCond(vcCond: Expr): Expr = vcCond match {
    case Implies(lhs, rhs) => rhs
    case _ => vcCond
  }
  
  /**
   * Removes the Let expression for post conditions that have multiple conjunction (it gives a value to "res").
   */
  private def removeLet(cond: Expr) : (Expr, Option[Identifier], Option[Expr]) = cond match {
    case Let(id, value, body) => (body, Some(id), Some(value))
    case _ => (cond, None, None)
  }
  
  /**
   * Separates the conjunctions of a post condition
   */
  private def separateConjunction(cond: Expr) : List[Expr] = cond match {
    case And(exprs) => exprs.toList.flatMap(separateConjunction(_))
    case _ => List(cond)
  }
  
  /**
   * Rebuild a let if original post-cond had it, for each separated conjunctions.
   */
  private def buildLet(letId: Option[Identifier], letBody: Option[Expr], conds: List[Expr]) : List[Expr] = letId match {
    case Some(id) => conds.map(Let(id, letBody.get, _))
    case None => conds
  }
  
  /**
   * Get a lists of post-condition from the function's verification condition, each holding only one conjunction (and the possible let for res)
   */
  private def getNewPostConds(vcCond: Expr) : List[(Expr,Expr)] = {
    val postCondExpr = getOnlyPostCond(vcCond)
    val (postCond,letId, letBody) = removeLet(postCondExpr)
    val separatedConds = separateConjunction(postCond)
    buildLet(letId,letBody,separatedConds).zip(separatedConds)
  }
  
  /**
   * Launches a new verification with a particular verification condition.
   * Returns true if the solver verified it.
   */
  def validateOneCond(cond: Expr, invalidRes: Map[Identifier, Expr], vctx: VerificationContext) : Boolean = {
    val eval = new CodeGenEvaluator(vctx.context, vctx.program)
    eval.eval(cond, invalidRes) match {
      case EvaluationResults.Successful(BooleanLiteral(b)) => b
      case _ => false
    }
  }

  /**
   * Gets the list of conjunctions violated by specific invalid results.
   */
  def getViolatedPostCond(invalidRes: Map[Identifier, Expr], vcCond: Expr, vctx: VerificationContext) : List[Expr] = {
    val newPostConds = getNewPostConds(vcCond)
    newPostConds.filter(x => !validateOneCond(x._1, invalidRes,vctx)).map(_._2)
  }
  /**
   * Checks whether the verification verify a post-condition or another condition
   */
  def postCondCheck(newObjRes: Option[Map[Identifier,Expr]], violatedPostCond : Option[List[Expr]], vc: VC, s: Solver, dt: Long) : VCResult = {
    vc.kind match {
      case Postcondition => VCResult(VCStatus.Invalid(s.getModel,newObjRes,violatedPostCond), Some(s), Some(dt))
      case _ => VCResult(VCStatus.Invalid(s.getModel,newObjRes,None), Some(s), Some(dt))
    }  
  }
}