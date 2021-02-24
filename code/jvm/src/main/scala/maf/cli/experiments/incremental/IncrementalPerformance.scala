package maf.cli.experiments.incremental

import maf.bench.scheme.IncrementalSchemeBenchmarkPrograms
import maf.core.Expression
import maf.language.CScheme.CSchemeParser
import maf.language.change.CodeVersion._
import maf.language.scheme.SchemeExp
import maf.modular.incremental.IncrementalConfiguration._
import maf.modular.incremental._
import maf.modular.incremental.scheme.SchemeAnalyses._
import maf.util.Reader
import maf.util.benchmarks._

import scala.concurrent.duration._

// The results of the evaluation.
sealed trait Result

case class Finished(mean: Long, stddev: Long) extends Result {
  override def toString: String = s"$mean±$stddev"
}

case object Timedout extends Result {
  override def toString: String = "∞"
}

case object NotRun extends Result {
  override def toString: String = " "
}

case object Errored extends Result {
  override def toString: String = "E"
}

trait IncrementalTime[E <: Expression] extends IncrementalExperiment[E] with TableOutput[Result] {

  // The maximal number of warm-up runs.
  val maxWarmupRuns = 5
  // The number of actually measured runs.
  val measuredRuns = 30

  // Indicate whether there is one or 2 incremental set-ups. Note that the setup must also be changed for warm-up.
  val multiInc = true

  val timeS: String = "ms"
  val propertiesS: List[String] = List(timeS)
  var results: Table[Result] = Table.empty.withDefaultValue(NotRun)
  val error: Result = Errored

  def runAnalysis(timedOut: Boolean, block: Timeout.T => Unit): Option[Double] = {
    print(if (timedOut) "x" else "*")
    if (timedOut) return None // A previous measurement already failed to complete.
    System.gc()
    val to = timeout()
    val time = Timer.timeOnly(block(to))
    if (to.reached) None
    else Some(time.toDouble / 1000000) // Return time in ms.
  }

  // A single program run with the analysis.
  def onBenchmark(file: String): Unit = {
    println(s"Testing $file")
    val program = parse(file)

    // Warm-up.

    // Use the same timeout for the entire warm-up.
    var timeoutWarmup: Timeout.T = timeout()
    var analyses: List[Analysis] = List()
    print(s"* Warm-up standard analysis (max. $maxWarmupRuns): ")
    for (w <- 1 to maxWarmupRuns) {
      print(s"$w ")
      System.gc()
      val a = analysis(program, noOptimisations)
      a.analyzeWithTimeout(timeoutWarmup)
      analyses = a :: analyses
    }
    print(s"\n* Warm-up incremental analysis (max. ${analyses.length}): ")
    timeoutWarmup = timeout().map(
      _ * (if (multiInc) 2 else 1)
    ) // Need to run two analyses, so double the time given (no guarantees on equal division between versions).
    for (w <- analyses.indices) {
      val a = analyses(w) // We need an analysis that has already been (partially) run.
      val b = a.deepCopy()
      b.configuration = allOptimisations
      print(s"*")
      System.gc()
      a.updateAnalysis(timeoutWarmup)
      if (multiInc) {
        print(s"* ")
        System.gc()
        b.updateAnalysis(timeoutWarmup)
      }
    }

    // Actual measurements.

    var timesInit: List[Double] = List()
    var timesInc1: List[Double] = List()
    var timesInc2: List[Double] = List()
    var timesRean: List[Double] = List()

    var inc1Timeout: Boolean = false
    var inc2Timeout: Boolean = false // For a second setup of the incremental analysis.
    var reanTimeout: Boolean = false

    print("\n* Measuring: ")
    for (i <- 1 to measuredRuns) {

      print(s"$i")
      var a = analysis(program, noOptimisations)

      // Run the initial analysis.
      runAnalysis(false, timeOut => a.analyzeWithTimeout(timeOut)) match {
        case Some(t) => timesInit = t :: timesInit
        case None =>
          println(" => Base analysis timed out.")
          results = results
            .add(file, columnName(timeS, initS), Timedout)
            .add(file, columnName(timeS, inc1S), NotRun)
            .add(file, columnName(timeS, inc2S), NotRun)
            .add(file, columnName(timeS, reanS), NotRun)
          return
      }

      val aCopy = a.deepCopy()
      aCopy.configuration = allOptimisations

      runAnalysis(inc1Timeout, timeOut => a.updateAnalysis(timeOut)) match {
        case Some(t) => timesInc1 = t :: timesInc1
        case None    => inc1Timeout = true
      }

      if (multiInc)
        runAnalysis(inc2Timeout, timeOut => aCopy.updateAnalysis(timeOut)) match {
          case Some(t) => timesInc2 = t :: timesInc2
          case None    => inc2Timeout = true
        }

      a = analysis(program, noOptimisations) // Create a new analysis and set the flag to "New". The configuration does not matter here.
      a.version = New
      runAnalysis(reanTimeout, timeOut => a.analyzeWithTimeout(timeOut)) match {
        case Some(t) => timesRean = t :: timesRean
        case None    => reanTimeout = true
      }
      print(" ")
    }

    // Process statistics.
    val init = Statistics.all(timesInit)
    val inc1 = Statistics.all(timesInc1)
    val inc2 = Statistics.all(timesInc2)
    val rean = Statistics.all(timesRean)

    results = results
      .add(file, columnName(timeS, initS), Finished(scala.math.round(init.mean), scala.math.round(init.stddev)))
      .add(file, columnName(timeS, inc1S), if (inc1Timeout) Timedout else Finished(scala.math.round(inc1.mean), scala.math.round(inc1.stddev)))
      .add(file, columnName(timeS, reanS), if (reanTimeout) Timedout else Finished(scala.math.round(rean.mean), scala.math.round(rean.stddev)))

    if (multiInc)
      results = results.add(file,
                            columnName(timeS, inc2S),
                            if (inc2Timeout) Timedout else Finished(scala.math.round(inc2.mean), scala.math.round(inc2.stddev))
      )

    println(s"\n    => $initS: ${init.mean} - $inc1S: ${inc1.mean} - $inc2S: ${inc2.mean} - $reanS: ${rean.mean}")
  }

  def createOutput(): String = results.prettyString(columns = List(initS, inc1S, inc2S, reanS).map(columnName(timeS, _)))
}

/* ************************** */
/* ***** Instantiations ***** */
/* ************************** */

object IncrementalSchemeModFPerformance extends IncrementalTime[SchemeExp] {
  override def benchmarks(): Set[String] = IncrementalSchemeBenchmarkPrograms.sequential

  override def analysis(e: SchemeExp, config: IncrementalConfiguration): Analysis = new IncrementalSchemeModFAnalysisTypeLattice(e, config)

  override def parse(string: String): SchemeExp = CSchemeParser.parse(Reader.loadFile(string))
  override def timeout(): Timeout.T = Timeout.start(Duration(10, MINUTES))
  val outputFile: String = s"performance/modf-type.txt"
}

object IncrementalSchemeModFCPPerformance extends IncrementalTime[SchemeExp] {
  override def benchmarks(): Set[String] = IncrementalSchemeBenchmarkPrograms.sequential

  override def analysis(e: SchemeExp, config: IncrementalConfiguration): Analysis = new IncrementalSchemeModFAnalysisCPLattice(e, config)

  override def parse(string: String): SchemeExp = CSchemeParser.parse(Reader.loadFile(string))
  override def timeout(): Timeout.T = Timeout.start(Duration(10, MINUTES))
  val outputFile: String = s"performance/modf-CP.txt"
}

object IncrementalSchemeModConcPerformance extends IncrementalTime[SchemeExp] {
  override def benchmarks(): Set[String] = IncrementalSchemeBenchmarkPrograms.threads

  override def analysis(e: SchemeExp, config: IncrementalConfiguration): Analysis = new IncrementalModConcAnalysisTypeLattice(e, config)

  override def parse(string: String): SchemeExp = CSchemeParser.parse(Reader.loadFile(string))
  override def timeout(): Timeout.T = Timeout.start(Duration(10, MINUTES))
  val outputFile: String = s"performance/modconc-type.txt"
}

object IncrementalSchemeModConcCPPerformance extends IncrementalTime[SchemeExp] {
  override def benchmarks(): Set[String] = IncrementalSchemeBenchmarkPrograms.threads

  override def analysis(e: SchemeExp, config: IncrementalConfiguration): Analysis = new IncrementalModConcAnalysisCPLattice(e, config)

  override def parse(string: String): SchemeExp = CSchemeParser.parse(Reader.loadFile(string))
  override def timeout(): Timeout.T = Timeout.start(Duration(10, MINUTES))
  val outputFile: String = s"performance/modconc-CP.txt"
}

object IncrementalSchemeModXPerformance {
  def main(args: Array[String]): Unit = {
    IncrementalSchemeModFPerformance.main(args)
    IncrementalSchemeModFCPPerformance.main(args)
    IncrementalSchemeModConcPerformance.main(args)
    IncrementalSchemeModConcCPPerformance.main(args)
  }
}
