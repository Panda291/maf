package maf.modular

import maf.core.*
//import maf.language.scheme.{SchemeBegin, SchemeExp, SchemeFuncall, SchemeIf, SchemeLet, SchemeParser}
import maf.language.scheme.*
import maf.modular.scheme.modf.*
import maf.util.benchmarks.Timeout
import maf.modular.worklist.FIFOWorklistAlgorithm
import maf.modular.scheme.*
import maf.modular.scheme.modf.SchemeModFComponent.Call

import scala.collection.mutable


trait ControlDependencyTracking extends DependencyTracking[SchemeExp] with BigStepModFSemantics {
  var condDependencies: mutable.Map[Identity, Set[Identity]] = mutable.Map().withDefaultValue(Set.empty)
  var functionCalls: mutable.Map[Identity, Set[Identity]] = mutable.Map().withDefaultValue(Set.empty)
  var probabilityModifiers: mutable.Map[Identity, Double] = mutable.Map().withDefaultValue(1.0)
  var lambdaList: List[Identity] = List()

  // https://www.baeldung.com/scala/merge-two-maps
  def combineIdentityMaps(a: Map[Identity, Set[Identity]], b: Map[Identity, Set[Identity]]): Map[Identity, Set[Identity]] = {
    a ++ b.map { case (k, v) => k -> (v ++ a.getOrElse(k, Set.empty)) }
  }

  lazy val fullDependencyMap: Map[Identity, Set[Identity]] = {
    val filteredCondDependencies = condDependencies.toMap
      .map(dep =>
        (dep._1,
          //dep._2.filter(e => (dep._1 == NoCodeIdentity && e != NoCodeIdentity) || (!lambdaList.contains(e) && e != NoCodeIdentity))))
          //dep._2.filter(e => (!lambdaList.contains(e) && e != NoCodeIdentity))))
          dep._2.filter(e => dep._1 != e && (!lambdaList.contains(e) && e != NoCodeIdentity))))

    combineIdentityMaps(filteredCondDependencies, functionCalls.toMap)
      .filter(dep => dep._1.pos.tag == Position.NoPTag)
      .map(dep =>
        (dep._1,
          dep._2.filter(e => e.pos.tag == Position.NoPTag)))
  }

  override def intraAnalysis(component: Component): ControlDependencyTrackingIntra

  def ComponentToIdentity(cmp: Component): Option[Identity] = {
    cmp match
      case Call(clo, _) => Some(clo._1.idn)
      case _ => None
  }

  trait ControlDependencyTrackingIntra extends BigStepModFIntra with DependencyTrackingIntra:
    override def eval(exp: SchemeExp): EvalM[Value] = {
      exp match
        case SchemeIf(cond, cons, alt, idn) if alt.idn == exp.idn => // no alternative exists
          condDependencies = condDependencies.++(Map(cond.idn -> Set(cons.idn)))
          condDependencies(idn) += cond.idn
          condDependencies(idn) += cons.idn
          probabilityModifiers = probabilityModifiers.++(Map(cond.idn -> 0.5)) // node itself forms chance, has same effect as branches doing so
        case SchemeIf(cond, cons, alt, idn) => // alternative exists
          condDependencies(idn) += cond.idn
          condDependencies(idn) += cons.idn
          condDependencies(idn) += alt.idn
          probabilityModifiers = probabilityModifiers.++(Map(cond.idn -> 0.5))
        case SchemeLambda(name, args, body, annotation, idn) =>
          condDependencies(idn) ++= body.map(_.idn)
          lambdaList ::= idn
        case SchemeVarArgLambda(name, args, vararg, body, annotation, idn) =>
          condDependencies(idn) ++= body.map(_.idn)
          lambdaList ::= idn
        case SchemeLet(bindings, body, idn) =>
          condDependencies(idn) ++= body.map(_.idn)
          condDependencies(idn) ++= bindings.map(_._2.idn)
        case SchemeLetStar(bindings, body, idn) =>
          condDependencies(idn) ++= body.map(_.idn)
          condDependencies(idn) ++= bindings.map(_._2.idn)
        case SchemeLetrec(bindings, body, idn) =>
          condDependencies(idn) ++= body.map(_.idn)
          condDependencies(idn) ++= bindings.map(_._2.idn)
        // SchemeNamedLet not a case class
        case SchemeSet(variable, value, idn) =>
          condDependencies(idn) += value.idn
        case SchemeSetLex(variable, lexAddr, value, idn) =>
          condDependencies(idn) += value.idn
        case SchemeBegin(exps, idn) =>
          condDependencies(idn) ++= exps.map(_.idn)
        case SchemeAssert(exp, idn) =>
          condDependencies(idn) += exp.idn
        case SchemeFuncall(f, args, idn) =>
          //              println(s"funcall $f from $idn to ${f.idn}")
          condDependencies(idn) ++= args.map(_.idn)
        case _ =>
      // TODO: confirm that objects such as "SchemeAnd" should also be managed. they seem to be transformed to if statements so might be managed
      super.eval(exp)
    }

    override def applyClosuresM(fun: Value,
                                args: List[(SchemeExp, Value)],
                                cll: Position.Position,
                                ctx: ContextBuilder = DefaultContextBuilder,
                               ): M[Value] = {
      val closures = lattice.getClosures(fun)
      closures.foreach(c => {
        functionCalls(SimpleIdentity(cll)) += c._1.idn
      })

      super.applyClosuresM(fun, args, cll, ctx)
    }
}


def newControlDependencyAnalysis(text: String) =
  val program = SchemeParser.parseProgram(text)
  new SimpleSchemeModFAnalysis(program)
    with SchemeModFNoSensitivity
    with SchemeConstantPropagationDomain
    with ControlDependencyTracking
    with FIFOWorklistAlgorithm[SchemeExp] {
    override def intraAnalysis(cmp: SchemeModFComponent) =
      new IntraAnalysis(cmp) with BigStepModFIntra with ControlDependencyTrackingIntra
  }
