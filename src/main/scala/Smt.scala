import java.io.{BufferedReader, BufferedWriter, InputStreamReader, OutputStreamWriter}
import java.nio.charset.StandardCharsets

case class Smt() {
  private val builder = new ProcessBuilder()
  builder.command("z3", "-smt2", "-in")
//  builder.command("tee", "/tmp/output.smt2")

  private var flushContexts = 0

  private val p: Process = builder.start()
  private val out: BufferedWriter = new BufferedWriter(new OutputStreamWriter(p.getOutputStream, StandardCharsets.UTF_8))
  private val in: BufferedReader = new BufferedReader(new InputStreamReader(p.getInputStream, StandardCharsets.UTF_8))

  def readLine(): String = in.readLine()

  private def write(text: String): Unit =
    if(flushContexts == 0) ???
    else {
      print(text)
      out.write(text)
    }

  private def flush[T](f: => T): T = {
    flushContexts += 1
    try {
      f
    } finally {
      flushContexts -= 1
      if(flushContexts == 0) {
        out.flush()
      }
    }
  }

  private def write(e: PureExp): Unit = e match {
    case smt: SmtExp => smt match {
      case PureApp(smtOp, args @ _*) =>
        write("(")
        write(smtOp)
        for(arg <- args) {
          write(" ")
          write(arg)
        }
        write(")")
      case PureLiteral(smtConst) =>
        write(smtConst)
      case Forall(binding, t, body) =>
        write("(forall ((")
        write(binding)
        write(" ")
        write(t)
        write(")) ")
        write(body)
        write(")")
    }
    case _ => ???
  }

  def setOption(key: String, value: String): Unit = flush {
    write("(set-option :")
    write(key)
    write(" ")
    write(value)
    write(")\n")
  }

  def declareEnum(t: String, values: Seq[String]): Unit = flush {
    write("(declare-datatype ")
    write(t)
    values match {
      case Nil => write("()")
      case value :: values =>
        write("(")
        write(value)
        write(")")
        for(value <- values) {
          write(" (")
          write(value)
          write(")")
        }
    }
    write(")\n")
  }

  def declareSort(name: String): Unit = flush {
    write("(declare-sort ")
    write(name)
    write(")\n")
  }

  def declare(name: String, t: String): PureLiteral = flush {
    write("(declare-const ")
    write(name)
    write(" ")
    write(t)
    write(")\n")
    PureLiteral(name)
  }

  def declareFun(name: String, retType: String, argTypes: Seq[String]): PartialApp = flush {
    write("(declare-fun ")
    write(name); write(" ")

    argTypes match {
      case Nil => write("()")
      case argType :: argTypes =>
        write("(")
        write(argType)
        for(argType <- argTypes) {
          write(" ")
          write(argType)
        }
        write(")")
    }

    write(" ")
    write(retType)
    write(")\n")

    PartialApp(name)
  }

  def assert(e: PureExp): Unit = {
    flush {
      write("(assert ")
      write(e)
      write(")\n")
    }
  }

  def push(): Unit = flush { write("(push)\n") }
  def pop(): Unit = flush { write("(pop)\n") }

  def scope[T](f: => T): T = {
    push()
    val result = f
    pop()
    result
  }

  def checkSat(): String = {
    flush { write("(check-sat)\n") }
    readLine()
  }

  def getModel(): String = {
    flush { write("(get-model)\n") }
    readLine()
  }
}