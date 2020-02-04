package scalaam.primitiveCompilation

import primitiveCompilation.ANFCompiler
import scalaam.primitiveCompilation.PrimSource._
import scalaam.primitiveCompilation.PrimTarget._
import scalaam.core._
import scalaam.language.scheme._
import scalaam.language.sexp._

object Test extends App {
  val program = "(define (length l) (let ((n (null? l))) (if n 0 (let ((c (cdr l))) (let ((len (length c))) (+ 1 len))))))"
  val program2 = "(define (length l) (if (null? l) 0 (+ 1 (length (cdr l)))))"
  println(program)
  val text = SchemeParser.parse(program)
  val source = PrimCompiler.toSource(text)
  println(source)
  val target = PrimCompiler.toTarget(source)
  println(PrimCompiler.toScala(target))
}

object PrimCompiler {

  type SE = PrimSource.Exp
  type TE = PrimTarget.Exp

  type SA = PrimSource.AExp
  type TA = PrimTarget.AExp

  trait CompilerException extends Exception

  case class  IllegalExpressionException(e: Expression) extends Exception // For expressions that should not occur in the language compiled in the current phase.
  case class ShouldNotEncounterException(e: Expression) extends Exception // For expressions that should not be encountered by the compiler in the current phase.

  case class PrimInfo(name: String, args: List[Identifier])
  type PI = PrimInfo

  def compile(exp: SchemeExp): String = toScala(toTarget(toSource(exp)))

  /////////////////////////////
  // FIRST COMPILATION PHASE //
  /////////////////////////////

  def toSource(exp: SchemeExp): (SE, PI) = {

    def valueToSource(v: Value): SE = v match {
      case ValueBoolean(bool) => AE(PrimSource.Boo(bool))
      case ValueInteger(int) => AE(PrimSource.Num(int))
    }

    def bodyToSource(exp: Expression): SE = exp match {
      case fc@SchemeFuncall(f, args, _) =>
        val argn = args.map(bodyToSource(_))
        if (!argn.forall(_.isInstanceOf[PrimSource.AE])) throw IllegalExpressionException(fc)
        val argv: PrimSource.Args = argn.map{case AE(ae) => ae}.toArray
        bodyToSource(f) match { // TODO maybe check arity?
          case AE(PrimSource.Var(Id(name))) if PrimitiveOperations.opNams.contains(name) => PrimSource.OpCall(PrimitiveOperations.ops.find(_.name == name).get, argv)
          case prim => PrimSource.PrimCall(prim, argv)
        }
      case SchemeIf(cond, cons, alt, _) => bodyToSource(cond) match {
        case AE(ae) => If(ae, bodyToSource(cons), bodyToSource(alt))
        case _ => throw IllegalExpressionException(cond) // TODO: support?
      }
      // For now, let behaves as a let* TODO?
      // Restrain a body to a single expression...
      // Important: use foldRight!
      case SchemeLet(bnd, body :: Nil, _) => bnd.foldRight(bodyToSource(body)){ case ((id, bnd), acc) => Let(PrimSource.Var(Id(id.name)), bodyToSource(bnd), acc) }
      case SchemeLetStar(bnd, body :: Nil, _) => bnd.foldRight(bodyToSource(body)){ case ((id, bnd), acc) => Let(PrimSource.Var(Id(id.name)), bodyToSource(bnd), acc) }
      // Dysfunctional begin now. TODO?
      case SchemeBegin(e :: Nil, _) => bodyToSource(e)
      case SchemeDefineVariable(id, exp, _) => Let(PrimSource.Var(Id(id.name)), bodyToSource(exp), ???) // TODO
      case SchemeVar(id) => AE(PrimSource.Var(Id(id.name)))
      case SchemeValue(v, _) => valueToSource(v)
      case id@Identifier(_, _) => throw ShouldNotEncounterException(id)
      case e => throw IllegalExpressionException(e)
    }

    exp match {
      // A primitive function is expected to be a function definition.
      case SchemeDefineFunction(nam, args, body :: Nil, _) => (bodyToSource(body), PrimInfo(nam.name, args))
      case e => throw IllegalExpressionException(e)
    }
  }

  //////////////////////////////
  // SECOND COMPILATION PHASE //
  //////////////////////////////

  def toTarget(src: (SE, PI)): (TE, PI) = {

    def AExpToTarget(ae: SA): TA = ae match {
      case PrimSource.Boo(b) => PrimTarget.Boo(b)
      case PrimSource.Num(n) => PrimTarget.Num(n)
      case PrimSource.Var(v) => PrimTarget.Var(v)
    }

    def varToTarget(v: PrimSource.Var): PrimTarget.Var = PrimTarget.Var(v.v)

    def toTarget(exp: SE): TE = exp match {
      case AE(ae) => Lat(Inj(AExpToTarget(ae)))
      case If(cond, cons, alt) =>
        val v0 = PrimTarget.Var()
        val v1 = PrimTarget.Var()
        val v2 = PrimTarget.Var()
        Bind(v0, Lat(Inj(AExpToTarget(cond))), // BindC
          Bind(v1, IfTrue(Inj(v0), toTarget(cons)), // BindC
            Bind(v2, IfFalse(Inj(v0), toTarget(alt)), // BindC
              Lat(Join(Inj(v1),
                Inj(v2))))))
      case Let(v, init, body) => Bind(varToTarget(v), toTarget(init), toTarget(body))
      case PrimSource.PrimCall(prim, args) => PrimTarget.PrimCall(toTarget(prim), Args(args.map(AExpToTarget)))
      case PrimSource.OpCall(op, args) => PrimTarget.OpCall(op, Args(args.map(AExpToTarget)))
    }

    (toTarget(src._1), src._2)
  }

  /////////////////////////////
  // THIRD COMPILATION PHASE //
  /////////////////////////////

  def toScala(tar: (TE, PI)): String = {
    val PrimInfo(name, args) = tar._2
    val string =
s"""object ${name.capitalize} extends NoStoreOperation($name, Some(${args.length})) {
  def appl(args: List[V]): MayFail[V, Error] = {
    val ${args.mkString(" :: ")} :: Nil = args
${tar._1.print(4)}
  }
  override def call(args: List[V]): MayFail[V, Error] = args match {
    case ${args.mkString(" :: ")} :: Nil => appl(args)
    case args => MayFail.failure(PrimitiveArityError($name, ${args.length}, args.length))
  }
}"""
    string
  }

}