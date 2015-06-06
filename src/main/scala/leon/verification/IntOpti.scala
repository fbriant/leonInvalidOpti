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

object IntOpti {
  
  private def computeBigSign(bigList: List[BigInt]) : Int = {
    val isBigPositive = bigList.filter(_ < 0).isEmpty
    val isBigNegative = bigList.filter(_ >= 0).isEmpty
    if (isBigPositive) {
      1
    } else if (isBigNegative){
      -1
    } else {
      0
    }
  }
  private def computeMinimalValue(list: List[Int]) : Int = computeMinimalValue(list.map(BigInt(_))).intValue()
  private def computeMinimalValue(bigList: List[BigInt]) : BigInt = {
    if (!bigList.isEmpty && bigList.filter(_ < 0).isEmpty) {
      bigList.min
    } else if (!bigList.isEmpty && bigList.filter(_ >= 0).isEmpty) {
      bigList.max
    } else {
      0
    }
  }
  
  private def getCompExprGr(expr: Expr) : List[(Identifier, BigInt)] = expr match {
    case GreaterThan(Variable(x), IntLiteral(i)) => List((x, BigInt(i+1)))
    case GreaterThan(Variable(x), InfiniteIntegerLiteral(i)) => List((x, i+1))
    case GreaterEquals(Variable(x), IntLiteral(i)) => List((x, BigInt(i)))
    case GreaterEquals(Variable(x), InfiniteIntegerLiteral(i)) => List((x, i+1))
    case LessThan(Variable(x), IntLiteral(i)) => List((x, BigInt(i-1)))
    case And(exprs) => exprs.toList.flatMap(getCompExprGr(_))
    case _ => Nil
  }
  private def getCompExprLs(expr: Expr) : List[(Identifier, BigInt)] = expr match {
    case LessThan(Variable(x), IntLiteral(i)) => List((x, i-1))
    case LessThan(Variable(x), InfiniteIntegerLiteral(i)) => List((x, i-1))
    case LessEquals(Variable(x), IntLiteral(i)) => List((x, BigInt(i)))
    case LessEquals(Variable(x), InfiniteIntegerLiteral(i)) => List((x, i))
    case And(exprs) => exprs.toList.flatMap(getCompExprLs(_))
    case _ => Nil
  }
  
  private def getRequirements(vcCond: Expr, sign: Int) : List[(Identifier,BigInt)] = {
    vcCond match {
      case Implies(lhs, _) => {
        if (sign > 0) {
          getCompExprGr(lhs)
        } else if (sign < 0) {
          getCompExprLs(lhs)
        } else {
          Nil
        }
      }
      case _ => Nil
    }
  }
  private def getUpdatedInt(list: List[(Identifier, Int)], vcCond: Expr) : List[Int] = getUpdatedBig(list.map(x => (x._1, BigInt(x._2))),vcCond).map(_.intValue())
  private def getUpdatedBig(list: List[(Identifier, BigInt)], vcCond: Expr) : List[BigInt] = {
    val sign = computeBigSign(list.map(_._2))
    if (sign == 0) {
      list.map(_._2)
    } else {
      val requirements = getRequirements(vcCond,sign)
      print(requirements)
      list.map(x => {
        val filter = requirements.filter(y => y._1 == x._1 && ((y._2 < 0 && x._2 < 0) || (y._2 >= 0 && x._2 >= 0)))     
        if (filter.isEmpty) {
          x._2   
        } else {
          if (sign > 0) {
            x._2 - filter.map(_._2).max
          } else {
            x._2 + filter.map(_._2).min
          }
        }
      })
    }
  }
  
  def computeNewInvalidRes(invalidRes: Map[Identifier, Expr], vcCond: Expr) : Map[Identifier, Expr] = {
    val invalidResSeq = invalidRes.toList
    val intInvalidRes = invalidResSeq.filter(x => x._2.isInstanceOf[IntLiteral]).map(x => (x._1, x._2.asInstanceOf[IntLiteral].value))
    val intInvalidResVal = intInvalidRes.map(_._2)
    val bigInvalidRes = invalidResSeq.filter(x => x._2.isInstanceOf[InfiniteIntegerLiteral]).map(x => (x._1, x._2.asInstanceOf[InfiniteIntegerLiteral].value))
    val bigInvalidResVal = bigInvalidRes.map(_._2)
    val intUpdated = getUpdatedInt(intInvalidRes, vcCond)
    val bigUpdated = getUpdatedBig(bigInvalidRes, vcCond)
    val intMinimalValue = computeMinimalValue(intUpdated)
    val bigMinimalValue = computeMinimalValue(bigUpdated)
    invalidRes.map(_ match {
      case (id, v) if v.isInstanceOf[InfiniteIntegerLiteral] => (id, InfiniteIntegerLiteral(v.asInstanceOf[InfiniteIntegerLiteral].value - bigMinimalValue))
      case (id, v) if v.isInstanceOf[IntLiteral] => (id, IntLiteral(v.asInstanceOf[IntLiteral].value - intMinimalValue))
      case (id, v) => (id, v)
      })
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
        val invalidMinRes: List[(Identifier, Int)] = invalidIntRes.map(x => (x._1, computeMinimalValue(x._2)))
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
  }
}