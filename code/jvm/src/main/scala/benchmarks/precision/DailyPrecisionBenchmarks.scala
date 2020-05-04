package scalaam.cli.benchmarks.precision

import scalaam.cli.benchmarks._
import scalaam.lattice._
import scalaam.language.scheme._
import scala.concurrent.duration._
import scalaam.util._

object DailyPrecisionBenchmarks extends AnalysisComparison[
    ConstantPropagation.I,
    ConstantPropagation.R,
    Concrete.B,
    ConstantPropagation.C,
    ConstantPropagation.S,
    Concrete.Sym
] {
    // analyses to compare
    def baseAnalysis(prg: SchemeExp): Analysis = 
        SchemeAnalyses.contextInsensitiveAnalysis(prg)
    def otherAnalyses() = List(
        (PrimitivesComparisonRQ4NamedFunctions.S_2CS_0, "S_2CS_0"),
        (SchemeAnalyses.adaptiveAnalysisPolicy3(_, 5), "adaptive-policy-3")
    )

    // benchmarks to run
    def benchmarks = PrimitivesBenchmarks.benchmarks

    // timeout configuration
    override def analysisTimeout() = Timeout.start(Duration(15, MINUTES)) //timeout for (non-base) analyses
    override def concreteTimeout() = Timeout.start(Duration(5, MINUTES))

    // entry point
    def main(args: Array[String]) = {
        benchmarks.foreach(runBenchmark)
        println(results.prettyString(format = _.map(_.toString()).getOrElse("TIMEOUT")))
        Writer.setDefaultWriter(Writer.open("benchOutput/daily-precision-benchmarks.csv"))
        Writer.write(results.toCSVString(format = _.map(_.toString()).getOrElse("TIMEOUT"), rowName = "benchmark"))
        Writer.closeDefaultWriter()
    }
}
