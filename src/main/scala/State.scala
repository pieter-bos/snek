import scala.collection.mutable

case object State {
  def empty(smt: Smt, program: Program): State = State(PureLiteral("$emp"), Map.empty, smt, program)
}

case class State
(
  heap: PureLiteral,
  store: Map[String, (PureLiteral, String)],

  smt: Smt,
  program: Program,
  uniq: mutable.Map[String, Int] = mutable.Map(),
) {
  def fresh(name: String, t: String): PureLiteral = {
    val id = uniq.getOrElseUpdate(name, 0)
    val freshName = s"$name@$id"
    uniq(name) += 1
    smt.declare(freshName, t)
    PureLiteral(freshName)
  }

  def havoc(k: String): State = {
    val t = store(k)._2
    copy(store = store.updated(k, (fresh(k, t), t)))
  }

  def havocAll(ks: Seq[String]): State =
    ks.foldLeft(this)(_.havoc(_))

  def declare(vars: Seq[(String, String)]): State =
    copy(store = store ++ vars.map { case (name, t) => name -> (fresh(name, t), t) }.toMap)

  def evalStructurally(e: PureExp): SmtExp = e match {
    case Forall(binding, t, body) => Forall(binding, t, evalStructurally(body))
    case PureApp(smtOp, args @ _*) => PureApp(smtOp, args.map(evalStructurally) : _*)
    case PureLiteral(smtConst) => PureLiteral(smtConst)
    case Local(name) => store(name)._1
    case Deref(obj, f) => PureApp("$field" + f + "Val", heap, evalStructurally(obj), PureLiteral(f))
  }

  def eval(e: PureExp, t: String, name: String): PureLiteral = {
    val ret = fresh(name, t)
    smt.assert(ret === evalStructurally(e))
    ret
  }

  def check(e: PureExp): Unit =
    smt.scope {
      smt.assert(!evalStructurally(e))
      smt.checkSat() match {
        case "unsat" => // ok
        case other => assert(false, s"Verdict: $other")
      }
    }

  def branch(condE: PureExp, whenTrue: => State, whenFalse: => State): State = {
    val cond = eval(condE, "Bool", "$cond")
    val trueState = smt.scope { smt.assert(cond); whenTrue }
    val falseState = smt.scope { smt.assert(cond); whenFalse }
    join(cond, trueState, falseState)
  }

  def join(cond: PureLiteral, whenTrue: State, whenFalse: State): State = {
    val heap = eval(cond.select(whenTrue.heap, whenFalse.heap), "$Heap", "$heap")
    val store = whenTrue.store.map {
      case (k, (_, t)) => k -> (eval(cond.select(whenTrue.store(k)._1, whenFalse.store(k)._1), t, k), t)
    }
    copy(heap = heap, store = store)
  }

  def inhale(assn: Assn): State = assn match {
    case Conj(left, right) => inhale(left).inhale(right)
    case Implies(ant, cons) => branch(ant, inhale(cons), this)
    case FieldAcc(Deref(obj, f), p) =>
      copy(heap = eval(PureApp("$heapAdd", heap, PureApp("$heaplet", obj, PureLiteral(f), p)), "$Heap", "$heap"))
    case exp: PureExp =>
      smt.assert(evalStructurally(exp))
      this
  }

  def exhale(assn: Assn): State = assn match {
    case Conj(left, right) => exhale(left).exhale(right)
    case Implies(ant, cons) => branch(ant, exhale(cons), this)
    case FieldAcc(Deref(obj, f), p) =>
      copy(heap = eval(PureApp("$heapSub", heap, PureApp("$heaplet", obj, PureLiteral(f), p)), "$Heap", "$heap"))
    case exp: PureExp =>
      check(exp)
      this
  }

  def execute(stat: Stat): State = stat match {
    case Block(stats @ _*) =>
      stats.foldLeft(this)(_.execute(_))
    case If(cond, whenTrue, whenFalse) =>
      branch(cond, execute(whenTrue), execute(whenFalse))
    case While(cond, invariant, body) =>
      val initial = this.havocAll(body.assigns.map(_.name).toSeq)

      initial
        .copy(heap = fresh("$heap", "$Heap"))
        .inhale(invariant &* cond)
        .execute(body)
        .exhale(invariant)

      initial
        .exhale(invariant)
        .inhale(invariant &* !cond)
    case AssignLocal(local, value) =>
      val replacement = eval(value, store(local)._2, local)
      copy(store = store.updated(local, (replacement, store(local)._2)))
    case AssignField(deref, value) =>
      ???
    case Inhale(assn) =>
      inhale(assn)
    case Exhale(assn) =>
      exhale(assn)
    case Assert(assn) =>
      exhale(assn)
      this
    case Call(methodId, argsE, outArgsE) =>
      val method = program.methods.find(_.name == methodId).get
      val args: Map[String, PureLiteral] = method.args.zip(argsE).map {
        case ((name, t), v) => name -> eval(v, t, name)
      }.toMap
      val outArgs: Map[String, String] = method.outArgs.zip(outArgsE).map {
        case ((name, t), local) => name -> local.name
      }.toMap
      this
        .exhale(method.requires.rewrite {
          case Local(name) if args.contains(name) => args(name)
        })
        .havocAll(outArgsE.map(_.name))
        .inhale(method.ensures.rewrite {
          case Local(name) if args.contains(name) => args(name)
          case Local(name) if outArgs.contains(name) => Local(outArgs(name))
        })
  }

  def verify(method: Method): State =
    declare(method.args)
      .inhale(method.requires)
      .declare(method.outArgs)
      .declare(method.locals)
      .execute(method.body)
      .exhale(method.ensures)
}