import leon.lang._
import leon.collection._
import leon.annotation._

object Robot {

  // From top left
  case class Position(x: BigInt, y: BigInt) {
    def +(o: Orientation) = o match {
      case North => Position(x, y-1)
      case East  => Position(x+1, y)
      case South => Position(x, y+1)
      case West  => Position(x-1, y)
    }
  }

  abstract class Orientation {
    def left = this match {
      case North => West
      case East  => North
      case South => East
      case West  => South
    }

    def right = this match {
      case North => East
      case East  => South
      case South => West
      case West  => North
    }
  }

  case object North extends Orientation
  case object East  extends Orientation
  case object South extends Orientation
  case object West  extends Orientation

  abstract class FireLevel {
    def level: BigInt = this match {
      case NoFire => 0
      case Fire1 => 1
      case Fire2 => 2
      case Fire3 => 3
      case Fire4 => 4
      case Fire5 => 5
    }

    def increase = this match {
      case NoFire => NoFire
      case Fire1 => Fire2
      case Fire2 => Fire3
      case Fire3 => Fire4
      case Fire4 => Fire5
      case Fire5 => Fire5
    }

    def temp:BigInt = level*100
  }

  case object NoFire extends FireLevel
  case object Fire1 extends FireLevel
  case object Fire2 extends FireLevel
  case object Fire3 extends FireLevel
  case object Fire4 extends FireLevel
  case object Fire5 extends FireLevel

  case class World(
    clock: BigInt,
    dimentions: Position,
    walls: Set[Position],
    persons: Set[Position],
    fires: Map[Position, FireLevel],
    rs: RobotState) {

    def personAt(pos: Position): Boolean = persons contains pos

    def wallAt(pos: Position): Boolean = walls contains pos

    def fireAt(pos: Position): FireLevel = {
      if (fires contains pos) {
        fires(pos)
      } else {
        NoFire
      }
    }

    def isWithinMap(p: Position): Boolean = {
      p.x >= 0 && p.x < dimentions.x &&
      p.y >= 0 && p.y < dimentions.y
    }
  }


  /*******************************************************************
   * Engine Component
   *******************************************************************/

  case class EngineState(pos: Position, dim: Position, orient: Orientation)

  abstract class EngineTransition
  case object EForward extends EngineTransition
  case object ERotateLeft extends EngineTransition
  case object ERotateRight extends EngineTransition
  case object EIdle        extends EngineTransition

  def engineStep(es: EngineState, t: EngineTransition) = t match {
    case EForward     => EngineState(es.pos + es.orient, es.dim, es.orient)
    case ERotateRight => EngineState(es.pos, es.dim, es.orient.right)
    case ERotateLeft  => EngineState(es.pos, es.dim, es.orient.left)
    case EIdle        => es
  }

  def engineSucc(es: EngineState): List[EngineTransition] = {
    if ((es.pos.x <= 0 && es.orient == West) ||
        (es.pos.y <= 0 && es.orient == North) ||
        (es.pos.x >= es.dim.x && es.orient == East) ||
        (es.pos.y >= es.dim.y && es.orient == South)) {
      List(ERotateLeft, ERotateRight, EIdle)
    } else {
      List(EForward, ERotateLeft, ERotateRight, EIdle)
    }
  }

  /*******************************************************************
   * Navigation Sensor Component
   *******************************************************************/

  case class NavSensorState(wall: Option[Boolean], person: Option[Boolean]) {
    def hasData = wall.isDefined && person.isDefined

    def validData(implicit w: World) = {
      val posFront = w.rs.es.pos + w.rs.es.orient

      val wallOk = wall match {
        case Some(wal) => wal == w.wallAt(posFront)
        case None() => true
      }

      val personOk = person match {
        case Some(per) => per == w.personAt(posFront)
        case None() => true
      }

      wallOk && personOk
    }
  }

  abstract class NavSensorTransition
  case object NSense   extends NavSensorTransition
  case object NForget  extends NavSensorTransition
  case object NIdle    extends NavSensorTransition


  def navSensorStep(ns: NavSensorState, t: NavSensorTransition)(implicit w: World) = t match {
    case NSense  =>
      val p = w.rs.es.pos + w.rs.es.orient
      NavSensorState(Some(w.wallAt(p)), Some(w.personAt(p)))

    case NForget =>
      NavSensorState(None(), None())

    case NIdle   =>
      ns
  }

  def navSensorSucc(ns: NavSensorState): List[NavSensorTransition] = {
    if (ns.hasData) {
      List(NForget, NIdle)
    } else {
      List(NSense, NIdle)
    }
  }

  /*******************************************************************
   * Heat Sensor Component
   *******************************************************************/

  case class HeatSensorState(fire: Option[FireLevel]) {
    def hasData = fire.isDefined

    def validData(implicit w: World) = {
      fire match {
        case Some(f) => w.fireAt(w.rs.es.pos + w.rs.es.orient) == f
        case None() => true
      }
    }
  }

  abstract class HeatSensorTransition
  case object HSense   extends HeatSensorTransition
  case object HForget  extends HeatSensorTransition
  case object HIdle    extends HeatSensorTransition

  def heatSensorStep(hs: HeatSensorState, t: HeatSensorTransition)(implicit w: World) = t match {
    case HSense  =>
      val p = w.rs.es.pos+w.rs.es.orient
      HeatSensorState(Some(w.fireAt(p)))

    case HForget =>
      HeatSensorState(None())

    case HIdle   =>
      hs
  }

  def heatSensorSucc(hs: HeatSensorState): List[HeatSensorTransition] = {
    if (hs.hasData) {
      List(HForget, HIdle)
    } else {
      List(HSense, HIdle)
    }
  }

  /*******************************************************************
   * Transmission Component
   *******************************************************************/

  case class TransmitterState(beacon: Option[Position]) {
    def hasData = beacon.isDefined
  }

  abstract class TransmitterTransition
  case object TTransmit extends TransmitterTransition
  case object TFound    extends TransmitterTransition
  case object TIdle     extends TransmitterTransition

  def transmitterStep(ts: TransmitterState, t: TransmitterTransition)(implicit w: World) = t match {
    case TTransmit  =>
      //require(ts.hasData)
      // transmit
      ts

    case TFound =>
      TransmitterState(Some(w.rs.es.pos + w.rs.es.orient))

    case TIdle =>
      ts
  }

  def transmitterSucc(ts: TransmitterState): List[TransmitterTransition] = {
    if (ts.hasData) {
      List(TTransmit, TFound)
    } else {
      List(TFound, TIdle)
    }
  }


  /*******************************************************************
   * Robot Component
   *******************************************************************/

  case class RobotState(
    es: EngineState,
    ns: NavSensorState,
    hs: HeatSensorState,
    ts: TransmitterState
  )

  case class RobotTransition(
    et: EngineTransition,
    nst: NavSensorTransition,
    hst: HeatSensorTransition,
    tt: TransmitterTransition
  )

  // Can wistand up to 300 degrees
  def safetyTemp:BigInt = 300

  // Temperature can increase by at most 100 degree while the robot moves
  def dTempMax:BigInt = 100

  // Glue that compose sensors, transmitter and engine to perform valid actions
  def validTransition(rs: RobotState, rt: RobotTransition): Boolean = {

    // 6) Sensors must be based on recent data
    val freshSensors = if (rt.et == EForward || rt.et == ERotateRight || rt.et == ERotateLeft) {
      rt.nst == NForget && rt.hst == HForget
    } else {
      true
    }

    // 2/3) We can move forward only if no wall was detected
    val forwardIfNoWall = (!(rt.et == EForward) || rs.ns.wall == Some(false))

    // 3) We don't exit the world
    val forwardIfNotOutOfMap = if (rt.et == EForward) {
      (rs.es.pos.x > 0 || rs.es.orient != West) &&
      (rs.es.pos.y > 0 || rs.es.orient != North) &&
      (rs.es.pos.x < rs.es.dim.x-1 || rs.es.orient != East) &&
      (rs.es.pos.y < rs.es.dim.y-1 || rs.es.orient != South)
    } else {
      true
    }

    // 4) We can move forward only if the cell is within heat limits
    val forwardIfNotHot = (!(rt.et == EForward) || rs.hs.fire.getOrElse(Fire5).temp <= safetyTemp-dTempMax)

    // 5) If we found, we read the position and transmit
    val transmitIfFound = if (rs.ns.person == Some(true)) {
      rt.tt == TFound
    } else {
      rt.tt == TTransmit || rt.tt == TIdle
    }

    forwardIfNotOutOfMap && freshSensors && forwardIfNoWall && forwardIfNotHot && transmitIfFound
  }

  def validWorld(implicit w: World): Boolean = {
    val dim = w.dimentions
    val pos = w.rs.es.pos

    dim.x > 0 && dim.y > 0 && dim == w.rs.es.dim &&
    w.isWithinMap(w.rs.es.pos)
  }

  def validState(implicit w: World): Boolean = {
    // 6) Sensors have consistent data
    val recentData = w.rs.ns.validData && w.rs.hs.validData

    // 2/3) We don't end up in a wall
    val notInWall = !w.wallAt(w.rs.es.pos)

    validWorld && recentData && notInWall
  }

  def validMove(from: World, to: World): Boolean = {
    require(from.clock <= to.clock && from.clock <= to.clock+1)

    val posFrom      = from.rs.es.pos
    val posFromFront = from.rs.es.pos + from.rs.es.orient
    val posTo        = to.rs.es.pos
    val posToFront   = to.rs.es.pos +to.rs.es.orient
  
    // 1) Robot must not rotate and move at the same time
    val dontRotateAndMove = (from.rs.es.pos == to.rs.es.pos) || (from.rs.es.orient == to.rs.es.orient)

    // 2) We don't leave the map
    val dontLeaveMap = to.isWithinMap(posTo)

    // 3) We don't run into a wall
    val dontRunInWall = !to.wallAt(posTo)

    // 4) We don't move to a cell that is too hot
    val dontBeCrazy = (from.fireAt(posFrom).temp > safetyTemp) || (to.fireAt(posTo).temp <= safetyTemp)

    // 5) If we found somebody, we record its position for transmission
    val transmitWhenFound = (from.rs.ns.person != Some(true)) || (to.rs.ts.beacon == Some(posFromFront))

    dontRotateAndMove && dontLeaveMap && dontRunInWall && dontBeCrazy && transmitWhenFound
  }

  def filterValid(rs: RobotState, rts: List[RobotTransition]): List[RobotTransition] = (rts match {
    case Cons(rt, rtt) =>
      val ts = filterValid(rs, rtt)

      if (validTransition(rs, rt)) {
        Cons(rt, ts)
      } else {
        ts
      }
    case Nil() => Nil[RobotTransition]()
  }) ensuring {
    res => allValid(rs, res)
  }

  def allValid(rs: RobotState, rts: List[RobotTransition]): Boolean = rts match {
    case Cons(rt, rtt) => validTransition(rs, rt) && allValid(rs, rtt)
    case Nil() => true
  }

  def robotSucc(rs: RobotState): List[RobotTransition] = {
    val ess  = engineSucc(rs.es)
    val nss  = navSensorSucc(rs.ns)
    val hss  = heatSensorSucc(rs.hs)
    val ts   = transmitterSucc(rs.ts)

    filterValid(rs, ||(ess, nss, hss, ts))
  } ensuring {
    res => allValid(rs, res)
  }

  def robotStep(rs: RobotState, rt: RobotTransition)(implicit w: World): RobotState = {
    RobotState(
      engineStep(rs.es, rt.et),
      navSensorStep(rs.ns, rt.nst),
      heatSensorStep(rs.hs, rt.hst),
      transmitterStep(rs.ts, rt.tt)
    )
  }

  def worldStep(w: World): World = {
    require(validWorld(w))

 //   val fires = allFires(w, Position(0, 0))
    World(w.clock + 1, w.dimentions, w.walls, w.persons, w.fires, w.rs) // FIXME
  } ensuring {
    w2 => {
      val pos1 = w.rs.es.pos
      val pos2 = w.rs.es.pos + w.rs.es.orient

      // in particular, we check that it holds for "interesting" positions
      fireEvolution(w.fireAt(pos1), w2.fireAt(pos1)) &&
      (!w.isWithinMap(pos2) || (fireEvolution(w.fireAt(pos2), w2.fireAt(pos2))))
    }
  }

  def allFires(w: World, p: Position): Map[Position, FireLevel] = {
    require(validWorld(w) && w.isWithinMap(p))

    (if (p.y == w.dimentions.y-1 && p.x == w.dimentions.x-1) { // last cell
      Map[Position, FireLevel]()
    } else if (p.x == w.dimentions.x-1) {
      allFires(w, Position(0, p.y+1))
    } else {
      allFires(w, Position(p.x+1, p.y))
    }).updated(p, fireModel(w, p))
  } ensuring {
    res => {
      val from = w.fireAt(p)
      val to   = if (res contains p) { res(p) } else { NoFire }
      fireEvolution(from, to)
    }
  }

  def fireModel(w: World, p: Position): FireLevel = {
    w.fireAt(p)
  } ensuring {
    res => fireEvolution(w.fireAt(p), res)
  }

  def fireEvolution(from: FireLevel, to: FireLevel): Boolean = {
    (from.temp <= to.temp) &&
    (to.temp <= from.temp + dTempMax)
  }

  def getBestTransition(rs: RobotState, ls: List[RobotTransition]): Option[RobotTransition] = {
    //require(allValid(rs, ls))

    if (ls.isEmpty) {
      None[RobotTransition]()
    } else {
      ls.find(rt => (rt.et == EForward) && validTransition(rs, rt)).orElse {
        Some(ls.head)
      }
    }
  } ensuring {
    res => res match {
      case Some(t) =>
        (ls.content contains t) && validTransition(rs, t)
      case None() =>
        ls.isEmpty
    }
  }

  def step(implicit w: World) = {
    require(validState)

    val rs = w.rs
    val transitions = robotSucc(rs)

    val ort = getBestTransition(rs, transitions)

    val nextRs = ort match {
      case Some(rt) =>
        robotStep(rs, rt)

      case None() =>
        rs
    }

    val w2 = World(w.clock, w.dimentions, w.walls, w.persons, w.fires, nextRs)

    (w2, ort)
  } ensuring {
    res =>
      val (nextW, ort) = res;
      (ort match {
        case Some(rt) =>
          validTransition(w.rs, rt) &&
          validMove(w, res._1)

        case None() =>
          true
      }) && validState(nextW)
  }

  def main(a: Array[String]): Unit = {
    val map = """|XXXXXXXXX
                 |XR FF   X
                 |X    PXXXX
                 |XXX F  F X
                 |X    X   X
                 |XX FPXXXXX
                 |XXXXXX""".stripMargin

    var initPos: Position = Position(0, 0)

    var walls   = Set[Position]()
    var mission = Set[Position]()
    var persons = Set[Position]()
    var fires   = Map[Position, FireLevel]()

    for ((line, y) <- map.split("\n").toSeq.zipWithIndex;
         (c, x) <- line.zipWithIndex) {

      val p = Position(x, y)

      c match {
        case 'R' =>
          initPos = p

        case 'X' =>
          walls += p

        case 'F' =>
          fires = fires.updated(p, Fire1)

        case 'P' =>
          persons += p

        case ' ' =>
      }

      if (c != 'X') {
        mission += p
      }
    }


    val dim = Position(walls.theSet.map(_.x).max+1, walls.theSet.map(_.y).max+1)

    val es  = EngineState(initPos, dim, North)
    val ns = NavSensorState(None(), None())
    val hs = HeatSensorState(None())
    val t  = TransmitterState(None())

    val rs = RobotState(es, ns, hs, t)

    implicit var w = World(0, dim, walls, persons, fires, rs)

    while(true) {
      print("\u001b[2J")
      val (nextW, otr) = step(w)
      w = nextW
      w = worldStep(w)
      draw(w, otr)
      Thread.sleep(1000l)
    }
  }

  @ignore
  def draw(w: World, ogt: Option[RobotTransition]): Unit = {
    val rs = w.rs

    def navSens(ns: NavSensorState): String = {
      ns.wall.map(v => if (v) "X" else  "_").getOrElse("?")
    }

    val o = (rs.es.orient match {
      case North => "^"
      case East  => ">"
      case South => "v"
      case West  => "<"
    })+" "+rs.es.pos.x+","+rs.es.pos.y

    print("Last Action: ")
    ogt match {
      case Some(gt) =>
        println(s"E: ${gt.et}, NS: ${gt.nst}, HS: ${gt.hst}, T: ${gt.tt}")

      case None() =>
        println("<stuck>")
    }
    println()
    println("Robot State: ")
    println(s" - Engine       : ${rs.es}")
    println(s" - Nav Sensor   : ${rs.ns}")
    println(s" - Heat Sensor  : ${rs.hs}")
    println(s" - Transmitter  : ${rs.ts}")

    println()
    println("Map:")
    println()

    for (y <- BigInt(0) until w.dimentions.y) {
      for(x <- BigInt(0) until w.dimentions.x) {

        val p = Position(x, y)

        val temp = w.fireAt(p).temp
        if (temp >= 100) {
          val level = temp.toInt/50+2
          val code = 0xE8 + Math.min(level, 23)
          print("\u001b[48;5;"+code+"m")
        }

        if (w.walls contains p) {
          print("XX")
        } else if (rs.es.pos == p) {
          print("R"+(rs.es.orient match {
            case North => "^"
            case South => "v"
            case East => ">"
            case West => "<"
          }))
        } else if (w.persons contains p) {
          print("HH")
        } else {
          print("  ")
        }

        if (temp >= 100) {
          print(Console.RESET)
        }

      }
      println
    }
  }

  def ||(ets: List[EngineTransition],
         nsts: List[NavSensorTransition],
         hsts: List[HeatSensorTransition],
         tts: List[TransmitterTransition]): List[RobotTransition] = {

    ets.flatMap { et =>
      nsts.flatMap { nst =>
        hsts.flatMap { hst =>
          tts.map { tt =>
            RobotTransition(et, nst, hst, tt)
          }
        }
      }
    }
  }
}
