import leon.annotation._
import leon.lang._

object Flo {
  sealed abstract class List
  case object Nil extends List
  case class Cons(value: Int, cons: List) extends List
  
  def Add(x: Int, y: Int) : Int = {
    x + y
  } ensuring(res => res == 6)
  
  def AddWithRequire1(x:Int, y:Int) : Int = {
    require(x > 2 && y > 2)
    x + y
  } ensuring(res => res == 5)
  
  def AddWithRequire2(x:Int, y:Int) : Int = {
    require(x > 1 && y > 1)
    x + y
  } ensuring(res => res == 5)
  
  def AddWithRequire3(x:Int, y:Int) : Int = {
    require(x > 1 && y > 6)
    x + y
  } ensuring(res => res == 5)
  
  def AddWithRequire4(x:Int, y:Int) : Int = {
    require(x > 6 && y > 1)
    x + y
  } ensuring(res => res == 5)
  
  def AddOneWithZAndConjs(x:Int, y:Int, z:Int) : Int = {
    x + y
  } ensuring(res => (res == 5 && res == 6) && (res != 4 && res !=3))
  
  def AddOneNeg(x:Int, y:Int) : Int = {
    -x + y
  } ensuring(res => res == 5)

  def dontGet3(x:Int, y:Int) : Int = {
    require(x != 0 && y != 0)
    x + y
  } ensuring(res => res != 3*x)
  
  def getNegAndPos(x: Int, y: Int) : Int = {
    require(x < 10000 && y < 10000 && x > -10000 && y > -10000) // we do not want overflow errors
    x + y
  } ensuring(res => res >= 0)
  
  def isConsOk(t: List) : Boolean = t match {
    case Cons(x, Cons(y, Nil)) => x != y+1
    case _ => true
  }
  
  def constNotOk(x: Int, y: Int) : List = {
    Cons(x, Cons(y, Nil))
  } ensuring(res => isConsOk(res))
 
}