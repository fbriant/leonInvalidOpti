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
import leon.verification.PostCondDiag._

import solvers._

object IntOpti {
  
  /**
   * Computes the sign of a list of integer (positive, negative or mixed sign).
   */
  private def computeIntSign(list: List[Int]) : Int = computeBigSign(list.map(BigInt(_)))
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
  /**
   * Computes the absolute minimal value of a list of integers.
   */
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
  /**
   * Get the requirements from the pre-conditions. Only when dealing with positive integers
   */
  private def getCompExprGr(expr: Expr) : List[(Identifier, BigInt)] = expr match {
    case GreaterThan(Variable(x), IntLiteral(i)) => List((x, BigInt(i+1)))
    case GreaterThan(Variable(x), InfiniteIntegerLiteral(i)) => List((x, i+1))
    case GreaterEquals(Variable(x), IntLiteral(i)) => List((x, BigInt(i)))
    case GreaterEquals(Variable(x), InfiniteIntegerLiteral(i)) => List((x, i+1))
    case And(exprs) => exprs.toList.flatMap(getCompExprGr(_))
    case _ => Nil
  }
  /**
   * Get the requirements from the pre-conditions. Only when dealing with negative integers
   */
  private def getCompExprLs(expr: Expr) : List[(Identifier, BigInt)] = expr match {
    case LessThan(Variable(x), IntLiteral(i)) => List((x, i-1))
    case LessThan(Variable(x), InfiniteIntegerLiteral(i)) => List((x, i-1))
    case LessEquals(Variable(x), IntLiteral(i)) => List((x, BigInt(i)))
    case LessEquals(Variable(x), InfiniteIntegerLiteral(i)) => List((x, i))
    case And(exprs) => exprs.toList.flatMap(getCompExprLs(_))
    case _ => Nil
  }
  /**
   * Get the requirements, if any, of a function's verification condition, according to the sign of the integers.
   */
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
  
  /**
   * Update the invalid result with the requirements, such that minimal value subtraction takes requirements into account.
   */
  private def getUpdatedInt(list: List[(Identifier, Int)], vcCond: Expr, sign: Int) : List[Int] = getUpdatedBig(list.map(x => (x._1, BigInt(x._2))),vcCond,sign).map(_.intValue())
  private def getUpdatedBig(list: List[(Identifier, BigInt)], vcCond: Expr, sign: Int) : List[BigInt] = {
    if (sign == 0) {
      list.map(_._2)
    } else {
      val requirements = getRequirements(vcCond,sign)
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
  
  /**
   * Compute a new simpler alternative model with minimal value subtraction.
   */
  def computeNewInvalidRes(invalidRes: Map[Identifier, Expr], vcCond: Expr) : Map[Identifier, Expr] = {
    val invalidResSeq = invalidRes.toList
    def computeIntMinimalValue() : (Int, Option[Int]) = {
      val intInvalidRes = invalidResSeq.filter(x => x._2.isInstanceOf[IntLiteral]).map(x => (x._1, x._2.asInstanceOf[IntLiteral].value))
      if (intInvalidRes.isEmpty) {
        (0, None)
      } else {
        val intInvalidResVal = intInvalidRes.map(_._2)
        val sign = computeIntSign(intInvalidResVal)
        if (sign == 0) {
          val positiveInvalidRes = intInvalidRes.filter(_._2 >= 0)
          val positiveUpdated = getUpdatedInt(positiveInvalidRes, vcCond, 1)
          val negativeInvalidRes = intInvalidRes.filter(_._2 < 0)
          val negativeUpdated = getUpdatedInt(negativeInvalidRes, vcCond, -1)
          (computeMinimalValue(positiveUpdated), Some(computeMinimalValue(negativeUpdated)))
        } else {
          val intUpdated = getUpdatedInt(intInvalidRes, vcCond, sign)
          (computeMinimalValue(intUpdated), None)
        }
      }
    }
    def computeBigMinimalValue() : (BigInt, Option[BigInt]) = {
      val bigInvalidRes = invalidResSeq.filter(x => x._2.isInstanceOf[InfiniteIntegerLiteral]).map(x => (x._1, x._2.asInstanceOf[InfiniteIntegerLiteral].value))
      if (bigInvalidRes.isEmpty) {
        (0, None)
      } else {
        val bigInvalidResVal = bigInvalidRes.map(_._2)
        val sign = computeBigSign(bigInvalidResVal)
        if (sign == 0) {
          val positiveInvalidRes = bigInvalidRes.filter(_._2 >= 0)
          val positiveUpdated = getUpdatedBig(positiveInvalidRes, vcCond, 1)
          val negativeInvalidRes = bigInvalidRes.filter(_._2 < 0)
          val negativeUpdated = getUpdatedBig(negativeInvalidRes, vcCond, -1)
          (computeMinimalValue(positiveUpdated), Some(computeMinimalValue(negativeUpdated)))
        } else {
          val bigUpdated = getUpdatedBig(bigInvalidRes, vcCond, sign)
          (computeMinimalValue(bigUpdated), None)
        }
       }
    }
    val (intMinimalValue, intNegMinimalValue) = computeIntMinimalValue()
    val (bigMinimalValue, bigNegMinimalValue) = computeBigMinimalValue()
    invalidRes.map(_ match {
      case (id, v) if v.isInstanceOf[InfiniteIntegerLiteral] => {
        val value = v.asInstanceOf[InfiniteIntegerLiteral].value
        bigNegMinimalValue match {
          case Some(neg) if (value < BigInt(0)) => (id, InfiniteIntegerLiteral(value - neg))
          case _ => (id, InfiniteIntegerLiteral(value - bigMinimalValue))
        }
      }
      case (id, v) if v.isInstanceOf[IntLiteral] => {
        val value = v.asInstanceOf[IntLiteral].value
        intNegMinimalValue match {
          case Some(neg) if (value < 0) => (id, IntLiteral(value - neg))
          case _ => (id, IntLiteral(value - intMinimalValue))
        }
      }
      case (id, v) => (id, v)
      })
  }
  
  private def findIntMinimalValue(id: Identifier, min : Int,oldMin: Int, max: Int, oldMax: Int, oldValue: Int, oldoldValue: Int, listOtherArgs: List[(Identifier, Expr)], vcCond: Expr, vctx: VerificationContext) : Int = {
    if (min + 1 == max || max == min || (min+max)/2 == oldValue || (min == oldMin && max == oldMax && oldValue == oldoldValue) || (min == -oldMin && min != 0) || (max == -oldMax && max != 0) || (oldValue == -oldoldValue && oldValue != 0)) {
      oldValue
    } else if (!validateOneCond(vcCond, ((id,IntLiteral((min+max)/2)) :: listOtherArgs).toMap, vctx)) {
      findIntMinimalValue(id, min,min, (min+max)/2, max, (min+max)/2, oldValue, listOtherArgs,vcCond,vctx)
    } else {
      findIntMinimalValue(id, (min+max)/2, min, max, max, oldValue, oldValue, listOtherArgs,vcCond, vctx)
    }
  }
  private def findBigMinimalValue(id: Identifier, min : BigInt, oldMin: BigInt, max: BigInt, oldMax: BigInt, oldValue : BigInt, oldoldValue: BigInt, listOtherArgs: List[(Identifier, Expr)], vcCond: Expr, vctx: VerificationContext) : BigInt = {
    if (min + 1 == max || max == min || (min+max)/2 == oldValue || (min == oldMin && max == oldMax && oldValue == oldoldValue) || (min == -oldMin && min != 0) || (max == -oldMax && max != 0) || (oldValue == -oldoldValue && oldValue != 0)) {
      oldValue
    } else if (!validateOneCond(vcCond, ((id,InfiniteIntegerLiteral((min+max)/2)) :: listOtherArgs).toMap, vctx: VerificationContext)) {
      findBigMinimalValue(id, min, min, (min+max)/2, max, (min+max)/2, oldValue, listOtherArgs,vcCond,vctx)
    } else {
      findBigMinimalValue(id, (min+max)/2, min, max, max, oldValue, oldValue, listOtherArgs,vcCond, vctx)
    }
  }
  
  private def computeBinarySearchIter(searchList: List[(Identifier, Expr)], updatedList: List[(Identifier, Expr)], vcCond: Expr, vctx: VerificationContext) : List[(Identifier, Expr)] = searchList match {
    case (id,v) :: xs if v.isInstanceOf[IntLiteral] => computeBinarySearchIter(xs, (id, IntLiteral(findIntMinimalValue(id, 0,0, v.asInstanceOf[IntLiteral].value,0, v.asInstanceOf[IntLiteral].value,0,xs ::: updatedList, vcCond,vctx))) :: updatedList,vcCond,vctx)
    case (id,v) :: xs if v.isInstanceOf[InfiniteIntegerLiteral] => computeBinarySearchIter(xs, (id, InfiniteIntegerLiteral(findBigMinimalValue(id, 0, 0, v.asInstanceOf[InfiniteIntegerLiteral].value, 0, v.asInstanceOf[InfiniteIntegerLiteral].value, 0,xs ::: updatedList, vcCond,vctx))) :: updatedList,vcCond,vctx)
    case (id,v) :: xs => computeBinarySearchIter(xs, (id,v) :: updatedList, vcCond, vctx)
    case Nil => updatedList
  }
  
  def computeBinarySearchInvalidRes(invalidRes: Map[Identifier, Expr], vcCond: Expr, vctx: VerificationContext) : Map[Identifier,Expr] = {
    computeBinarySearchIter(invalidRes.toList, Nil, vcCond, vctx).toMap
  }
  
  
  /**
   * Computes new invalid results with local minimal value substraction inside a CaseClass.
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
  
  def getInvalidResultsOptimisation(vcCond: Expr, s: Solver, vctx: VerificationContext, vConds: List[Expr]) : (Map[Identifier,Expr],Expr) = {
    def getBetterModel(model1: Map[Identifier, Expr], model2: Map[Identifier, Expr]) : Map[Identifier,Expr] = {
      def modelUnfold(model: Map[Identifier, Expr]) : BigInt = {
        model.map(_ match {
          case (id, IntLiteral(i)) => (id, InfiniteIntegerLiteral(i))
          case (id, v) => (id, v)
        }).filter(_._2.isInstanceOf[InfiniteIntegerLiteral]).map(_._2.asInstanceOf[InfiniteIntegerLiteral].value).reduceLeft((x,y) => x.abs + y.abs)
      }
      val newViolatedPostCond1 = getViolatedPostCond(model1,getNewVcCond(model1,vcCond),vctx)
      val newViolatedPostCond2 = getViolatedPostCond(model2,getNewVcCond(model2,vcCond),vctx)
      if(modelUnfold(model1) > modelUnfold(model2)) {
        if (newViolatedPostCond2 == vConds) {
          model2
        } else {
          model1
        }
      } else {
        if (newViolatedPostCond1 == vConds) {
          model1
        } else {
          model2
        }
      }

    }
    val newIntResMVS = computeNewInvalidRes(s.getModel,vcCond)
    val newIntResBS = computeBinarySearchInvalidRes(s.getModel, vcCond, vctx)
    val newIntRes = getBetterModel(newIntResMVS, newIntResBS)
    val newObjRes = computeNewObjectInvalidRes(newIntRes)
    (newObjRes, getNewVcCond(newObjRes,vcCond))
  }
}