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
  var lambdaChildren: mutable.Map[Identity, Set[Identity]] = mutable.Map().withDefaultValue(Set.empty)

  // https://www.baeldung.com/scala/merge-two-maps
  def combineIdentityMaps(a: Map[Identity, Set[Identity]], b: Map[Identity, Set[Identity]]): Map[Identity, Set[Identity]] = {
    a ++ b.map { case (k, v) => k -> (v ++ a.getOrElse(k, Set.empty)) }
  }

  lazy val fullDependencyMap: Map[Identity, Set[Identity]] = {
    val filteredCondDependencies = condDependencies.toMap
      .map(dep =>
        (dep._1,
          dep._2.filter(e => dep._1 != e && (!lambdaList.contains(e) && e != NoCodeIdentity))))

    combineIdentityMaps(filteredCondDependencies, functionCalls.toMap)
      .filter(dep => dep._1.pos.tag == Position.NoPTag)
      .map(dep =>
        (dep._1,
          dep._2.filter(e => e.pos.tag == Position.NoPTag)))
  }

  lazy val reverseDependencyMap: Map[Identity, Set[Identity]] = {
    val resultMap: mutable.Map[Identity, Set[Identity]] = mutable.Map().withDefaultValue(Set.empty)
    fullDependencyMap.foreach((k,vs) => {
      vs.foreach(v => {
        resultMap(v) += k
      })
    })
    resultMap.toMap
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
          addDependency(Set(cond.idn, cons.idn), idn)
          probabilityModifiers = probabilityModifiers.++(Map(cons.idn -> 0.5))
          probabilityModifiers = probabilityModifiers.++(Map(alt.idn -> 0.5))
        case SchemeIf(cond, cons, alt, idn) => // alternative exists
          addDependency(Set(cond.idn, cons.idn, alt.idn), idn)
          probabilityModifiers = probabilityModifiers.++(Map(cons.idn -> 0.5))
          probabilityModifiers = probabilityModifiers.++(Map(alt.idn -> 0.5))
        case SchemeLambda(name, args, body, annotation, idn) =>
          addDependency(body.map(_.idn), idn, true)
          lambdaList ::= idn
        case SchemeVarArgLambda(name, args, vararg, body, annotation, idn) =>
          addDependency(body.map(_.idn), idn, true)
          lambdaList ::= idn
        case SchemeLet(bindings, body, idn) =>
          addDependency(body.map(_.idn), idn)
          addDependency(bindings.map(_._2.idn), idn)
        case SchemeLetStar(bindings, body, idn) =>
          addDependency(body.map(_.idn), idn)
          addDependency(bindings.map(_._2.idn), idn)
        case SchemeLetrec(bindings, body, idn) =>
          addDependency(body.map(_.idn), idn)
          addDependency(bindings.map(_._2.idn), idn)
        case SchemeSet(variable, value, idn) =>
          addDependency(Set(value.idn), idn)
        case SchemeSetLex(variable, lexAddr, value, idn) =>
          addDependency(Set(value.idn), idn)
        case SchemeBegin(exps, idn) =>
          addDependency(exps.map(_.idn), idn)
        case SchemeAssert(exp, idn) =>
          addDependency(Set(exp.idn), idn)
        case SchemeFuncall(f, args, idn) =>
          addDependency(args.map(_.idn), idn)
        case _ =>
      super.eval(exp)
    }

    private def addLambdaChildren(idns: Iterable[Identity], parent: Identity, isParentLambda: Boolean = false): Unit = {
      if isParentLambda then
        lambdaChildren (parent) ++= idns.filter(e => e != parent && e != NoCodeIdentity)
      else
        lambdaChildren.foreach((k, v) => {
          if v.contains(parent) then
            lambdaChildren(k) ++= idns.filter(e => e != parent && e != NoCodeIdentity)
        })
    }

    private def addDependency(idns: Iterable[Identity], parent: Identity, isParentLambda: Boolean = false): Unit = {
      if parent.pos.tag == Position.NoPTag then
        val filteredIdns = idns.filter(_.pos.tag == Position.NoPTag)
        addLambdaChildren(filteredIdns, parent, isParentLambda)
        condDependencies(parent) ++= filteredIdns
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
