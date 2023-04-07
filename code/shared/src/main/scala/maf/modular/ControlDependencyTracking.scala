package maf.modular

import maf.core._
import maf.language.scheme.{SchemeExp, SchemeIf, SchemeBegin, SchemeFuncall}
import maf.modular.scheme.modf.*
import maf.util.benchmarks.Timeout
import maf.modular.worklist.FIFOWorklistAlgorithm
import maf.modular.scheme.*
import maf.language.scheme.SchemeParser


trait ControlDependencyTracking extends DependencyTracking[SchemeExp] with BigStepModFSemantics {
  var condDependencies: Map[Identity, Set[Identity]] = Map().withDefaultValue(Set.empty)
  var debugExpressionSet: Set[SchemeExp] = Set.empty

  override def intraAnalysis(component: Component): ControlDependencyTrackingIntra

  trait ControlDependencyTrackingIntra extends BigStepModFIntra with DependencyTrackingIntra:
//        abstract override def analyzeWithTimeout(timeout: Timeout.T): Unit = {
//          expr(component) match
//    //        case SchemeIf(cond, cons, alt, idn) => { debugExpressionSet += cond
//    //                                                 debugExpressionSet += cons
//    //                                                 debugExpressionSet += alt }
//            case SchemeIf(_,_,_,_) => debugExpressionSet += expr(component).asInstanceOf[SchemeExp]
//            case _ => debugExpressionSet += expr(component).asInstanceOf[SchemeExp]
//          super.analyzeWithTimeout(timeout)
//        }

    override def eval(exp: SchemeExp): EvalM[Value] = {
          exp match
            case SchemeIf(cond, cons, alt, idn) if alt.idn == exp.idn =>
              condDependencies = condDependencies.++(Map(cond.idn -> Set(cons.idn)))
            case SchemeIf(cond, cons, alt, idn) => // alt exists
              condDependencies = condDependencies.++(Map(cond.idn -> Set(cons.idn, alt.idn)))
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
