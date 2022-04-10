case object Main {
  def forall(name: String, t: String, f: PureExp => PureExp): PureExp =
    Forall(name, t, f(PureLiteral(name)))

  val select: PartialApp = PartialApp("ite")
  val none: PureLiteral = PureLiteral("0.0")
  val write: PureLiteral = PureLiteral("1.0")

  def prelude(smt: Smt, fields: Map[String, String]): Unit = {
    smt.setOption("trace", "true")
    smt.setOption("proof", "true")
    smt.setOption("smt.mbqi", "false")

    smt.declareSort("$Heap")
    smt.declareEnum("$Field", fields.keys.toSeq)
    smt.declareSort("$Ref")

    val fieldPerm = smt.declareFun("$fieldPerm", "Real", Seq("$Heap", "$Ref", "$Field"))

    val fieldLookup: Map[String, PartialApp] =
      for((field, t) <- fields)
        yield field -> smt.declareFun("$field" + field + "Val", t, Seq("$Heap", "$Ref", "$Field"))

    smt.assert(forall("h", "$Heap", h =>
      forall("ref", "$Ref", ref =>
        forall("f", "$Field", f =>
          fieldPerm(h, ref, f) >= none
        )
      )
    ))

    val heapAdd = smt.declareFun("$heapAdd", "$Heap", Seq("$Heap", "$Heap"))

    smt.assert(forall("h1", "$Heap", h1 => forall("h2", "$Heap", h2 =>
      forall("ref", "$Ref", ref => forall("f", "$Field", f =>
        fieldPerm(heapAdd(h1, h2), ref, f) === fieldPerm(h1, ref, f) + fieldPerm(h2, ref, f)
    )))))

    for(lookup <- fieldLookup.values) {
      smt.assert(forall("h1", "$Heap", h1 => forall("h2", "$Heap", h2 =>
        forall("ref", "$Ref", ref => forall("f", "$Field", f =>
          fieldPerm(heapAdd(h1, h2), ref, f) > none implies (
            lookup(heapAdd(h1, h2), ref, f) === lookup(h1, ref, f) &&
            lookup(heapAdd(h1, h2), ref, f) === lookup(h2, ref, f)
          )
      )))))
    }

    val heapSub = smt.declareFun("$heapSub", "$Heap", Seq("$Heap", "$Heap"))

    smt.assert(forall("h1", "$Heap", h1 => forall("h2", "$Heap", h2 =>
      forall("ref", "$Ref", ref => forall("f", "$Field", f =>
        fieldPerm(h1, ref, f) >= fieldPerm(h2, ref, f) implies
        fieldPerm(heapSub(h1, h2), ref, f) === fieldPerm(h1, ref, f) - fieldPerm(h2, ref, f)
    )))))

    for(lookup <- fieldLookup.values) {
      smt.assert(forall("h1", "$Heap", h1 => forall("h2", "$Heap", h2 =>
        forall("ref", "$Ref", ref => forall("f", "$Field", f =>
          fieldPerm(heapSub(h1, h2), ref, f) > none implies (
            lookup(heapSub(h1, h2), ref, f) === lookup(h1, ref, f) &&
            lookup(heapSub(h1, h2), ref, f) === lookup(h2, ref, f)
          )
      )))))
    }

    val emp = smt.declare("$emp", "$Heap")

    smt.assert(forall("ref", "$Ref", ref => forall("f", "$Field", f =>
      fieldPerm(emp, ref, f) === none
    )))

    val heaplet = smt.declareFun("$heaplet", "$Heap", Seq("$Ref", "$Field", "Real"))

    smt.assert(forall("ref", "$Ref", ref => forall("qref", "$Ref", qref =>
      forall("f", "$Field", f => forall("qf", "$Field", qf =>
        forall("p", "Real", p =>
          select(
            none <= p && p <= write,
            fieldPerm(heaplet(ref, f, p), qref, qf) ===
              select(ref === qref && f === qf, p, none),
            heaplet(ref, f, p) === emp
          )
    ))))))

//    for((name, lookup) <- fieldLookup) {
//      val update = smt.declareFun("$field" + name + "Update", "$Heap", Seq("$Heap", "$Ref", fields(name)))
//
//      smt.assert(forall("heap", "$Heap", h => forall("ref", "$Ref", ref => forall("v", fields(name), v =>
//        update(h, ref, v)
//      ))))
//    }
  }

  def verify(program: Program): Unit = {
    val smt = Smt()
    prelude(smt, program.fields)
    program.methods.foreach(State.empty(smt, program).verify(_))
  }

  def main(args: Array[String]): Unit = {
    verify(Program(Map("f" -> "Int"),
      Method(
        name = "test",
        args = Seq(

        ),
        outArgs = Nil,
        requires = PureLiteral("true"),
        ensures = PureLiteral("true"),
        locals = Seq(
          "x" -> "Int",
          "y" -> "Int",
        ),
        body = Block(
          AssignLocal("x", PureLiteral("5")),
          Assert(Local("x") === PureLiteral("5")),
          AssignLocal("y", Local("x") + Local("x")),
          Assert(Local("y") === PureLiteral("10")),
          AssignLocal("x", PureLiteral("8")),
          Assert(Local("y") === PureLiteral("10")),
        ),
      )
    ))
  }
}
