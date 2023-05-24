package maf.modular

import maf.core.*
//import maf.language.scheme.{SchemeBegin, SchemeExp, SchemeFuncall, SchemeIf, SchemeLet, SchemeParser}
import maf.language.scheme.*
import maf.modular.scheme.modf.*
import maf.util.benchmarks.Timeout
import maf.modular.worklist.FIFOWorklistAlgorithm
import maf.modular.scheme.*

import scala.collection.mutable


trait ControlDependencyTracking extends DependencyTracking[SchemeExp] with BigStepModFSemantics {
  var condDependencies: mutable.Map[Identity, Set[Identity]] = mutable.Map().withDefaultValue(Set.empty)
//  var funcDependencies: mutable.Map[Identity, Set[Identity]] = mutable.Map().withDefaultValue(Set.empty)
  var probabilityModifiers: mutable.Map[Identity, Double] = mutable.Map().withDefaultValue(1.0)

  override def intraAnalysis(component: Component): ControlDependencyTrackingIntra

  trait ControlDependencyTrackingIntra extends BigStepModFIntra with DependencyTrackingIntra:
    override def eval(exp: SchemeExp): EvalM[Value] = {
          exp match
            case SchemeIf(cond, cons, alt, idn) if alt.idn == exp.idn => // no alternative exists
              condDependencies = condDependencies.++(Map(cond.idn -> Set(cons.idn)))
              condDependencies(cond.idn) += cons.idn
              probabilityModifiers = probabilityModifiers.++(Map(cond.idn -> 0.5)) // node itself forms chance, has same effect as branches doing so
            case SchemeIf(cond, cons, alt, idn) => // alternative exists
              condDependencies(cond.idn) += cons.idn
              condDependencies(cond.idn) += alt.idn
              probabilityModifiers = probabilityModifiers.++(Map(cond.idn -> 0.5))
            case SchemeLambda(name, args, body, annotation, idn) =>
              condDependencies(idn) ++= body.map(_.idn)
            case SchemeVarArgLambda(name, args, vararg, body, annotation, idn) =>
              condDependencies(idn) ++= body.map(_.idn)
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
              condDependencies(idn) ++= args
            case _ =>
              // TODO: confirm that objects such as "SchemeAnd" should also be managed. they seem to be transformed to if statements so might be managed
          super.eval(exp)
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
