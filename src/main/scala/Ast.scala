sealed trait Assn {
  def &*(other: Assn): Assn = Conj(this, other)

  def rewrite(f: PartialFunction[Assn, Assn]): Assn = {
    val pureF = f.asInstanceOf[PartialFunction[PureExp, PureExp]]
    f.lift(this) match {
      case Some(value) => value
      case None => this match {
        case Conj(left, right) => Conj(left.rewrite(f), right.rewrite(f))
        case Implies(ant, cons) => Implies(ant.rewrite(pureF), cons.rewrite(f))
        case FieldAcc(Deref(obj, f), p) => FieldAcc(Deref(obj.rewrite(pureF), f), p.rewrite(pureF))
        case exp: PureExp => exp.rewrite(pureF)
      }
    }
  }
}
case class Conj(left: Assn, right: Assn) extends Assn
case class Implies(ant: PureExp, cons: Assn) extends Assn
case class FieldAcc(deref: Deref, p: PureExp) extends Assn

sealed trait PureExp extends Assn {
  def +(other: PureExp): PureExp = PureApp("+", this, other)
  def -(other: PureExp): PureExp = PureApp("-", this, other)
  def *(other: PureExp): PureExp = PureApp("*", this, other)
  def /(other: PureExp): PureExp = PureApp("/", this, other)

  def &&(other: PureExp): PureExp = PureApp("and", this, other)
  def ||(other: PureExp): PureExp = PureApp("or", this, other)
  def unary_! : PureExp = PureApp("not", this)
  def implies(other: PureExp): PureExp = PureApp("=>", this, other)
  def select(left: PureExp, right: PureExp): PureExp = PureApp("ite", this, left, right)

  def ===(other: PureExp): PureExp = PureApp("=", this, other)
  def !==(other: PureExp): PureExp = PureApp("not", PureApp("=", this, other))
  def >=(other: PureExp): PureExp = PureApp(">=", this, other)
  def >(other: PureExp): PureExp = PureApp(">", this, other)
  def <=(other: PureExp): PureExp = PureApp("<=", this, other)
  def <(other: PureExp): PureExp = PureApp("<", this, other)

  def rewrite(f: PartialFunction[PureExp, PureExp]): PureExp =
    f.lift(this) match {
      case Some(value) => value
      case None => this match {
        case Forall(binding, t, body) => Forall(binding, t, body.rewrite(f))
        case PureApp(smtOp, args@_*) => PureApp(smtOp, args.map(_.rewrite(f)) : _*)
        case PureLiteral(smtConst) => PureLiteral(smtConst)
        case Local(name) => Local(name)
        case Deref(obj, field) => Deref(obj.rewrite(f), field)
        case CurPerm(Deref(obj, field)) => CurPerm(Deref(obj.rewrite(f), field))
      }
    }
}

sealed trait SmtExp extends PureExp
case class Forall(binding: String, t: String, body: PureExp) extends SmtExp
case class PureApp(smtOp: String, args: PureExp*) extends SmtExp
case class PureLiteral(smtConst: String) extends SmtExp

case class PartialApp(smtOp: String) {
  def apply(args: PureExp*): PureExp = PureApp(smtOp, args : _*)
}

case class Local(name: String) extends PureExp
case class Deref(obj: PureExp, f: String) extends PureExp
case class CurPerm(deref: Deref) extends PureExp

sealed trait Stat {
  def assigns: Set[Local] = this match {
    case Block(stats@_*) => stats.flatMap(_.assigns).toSet
    case If(_, whenTrue, whenFalse) => whenTrue.assigns ++ whenFalse.assigns
    case While(_, _, body) => body.assigns
    case AssignLocal(local, _) => Set(Local(local))
    case AssignField(_, _) => Set.empty
    case Inhale(_) => Set.empty
    case Exhale(_) => Set.empty
    case Assert(_) => Set.empty
    case Call(_, _, outArgs) => outArgs.toSet
  }
}

case class Block(stats: Stat*) extends Stat
case class If(cond: PureExp, whenTrue: Stat, whenFalse: Stat) extends Stat
case class While(cond: PureExp, invariant: Assn, body: Stat) extends Stat

case class AssignLocal(local: String, value: PureExp) extends Stat
case class AssignField(deref: Deref, value: PureExp) extends Stat

case class Inhale(assn: Assn) extends Stat
case class Exhale(assn: Assn) extends Stat
case class Assert(assn: Assn) extends Stat

case class Call(method: String, args: Seq[PureExp], outArgs: Seq[Local]) extends Stat

case class Method(name: String,
                  args: Seq[(String, String)],
                  outArgs: Seq[(String, String)],
                  requires: Assn,
                  ensures: Assn,
                  locals: Seq[(String, String)],
                  body: Stat)

case class Program(fields: Map[String, String], methods: Method*)