package maf.modular

import maf.core._
import maf.language.scheme.{SchemeExp, SchemeIf, SchemeBegin, SchemeFuncall}
import maf.modular.scheme.modf.*
import maf.util.benchmarks.Timeout
import maf.modular.worklist.FIFOWorklistAlgorithm
import maf.modular.scheme.*
import maf.language.scheme.SchemeParser
import scala.collection.mutable


trait ControlDependencyTracking extends DependencyTracking[SchemeExp] with BigStepModFSemantics {
  var condDependencies: mutable.Map[Identity, Set[Identity]] = mutable.Map().withDefaultValue(Set.empty)
  var debugExpressionSet: Set[SchemeExp] = Set.empty

  override def intraAnalysis(component: Component): ControlDependencyTrackingIntra

  trait ControlDependencyTrackingIntra extends BigStepModFIntra with DependencyTrackingIntra:
    override def eval(exp: SchemeExp): EvalM[Value] = {
          exp match
            case SchemeIf(cond, cons, alt, idn) if alt.idn == exp.idn =>
              condDependencies = condDependencies.++(Map(cond.idn -> Set(cons.idn)))
              condDependencies(cond.idn) += cons.idn
            case SchemeIf(cond, cons, alt, idn) => // alt exists
              condDependencies(cond.idn) += cons.idn
              condDependencies(cond.idn) += alt.idn
            case _ =>
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
