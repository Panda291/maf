package scalaam.language.scheme

import scalaam.core._
import scalaam.language.sexp._

/**
  * Trait that provides a method to compile an s-expression into a standard Scheme expression.
  */
trait BaseSchemeCompiler {
  class SchemeCompilerException(reason: String, position: Identity) extends Exception(reason)
  import scala.util.control.TailCalls._

  /**
    * Reserved keywords
    */
  def reserved: List[String] =
    List("lambda", "if", "let", "let*", "letrec", "cond", "case", "set!", "begin", "define", "do", "when", "unless")

  def compile(exp: SExp): SchemeExp = this._compile(exp).result

  def _compile(exp: SExp): TailRec[SchemeExp] = exp match {
    case SExpPair(SExpId(Identifier("quote", _)), SExpPair(quoted, SExpValue(ValueNil, _), _), _) =>
      tailcall(expandQuoted(quoted))
    case SExpPair(SExpId(Identifier("quote", _)), _, _) =>
      throw new SchemeCompilerException(s"Invalid Scheme quote: $exp", exp.idn)
    case SExpPair(SExpId(Identifier("quasiquote", _)), SExpPair(quasiquoted, SExpValue(ValueNil, _), _), _) =>
      tailcall(expandQuasiquoted(quasiquoted,1))
    case SExpPair(SExpId(Identifier("quasiquote", _)), _, _) =>
      throw new SchemeCompilerException(s"Invalid Scheme quasiquote: $exp", exp.idn)
    case SExpPair(
        SExpId(Identifier("lambda", _)),
        SExpPair(args, body, _),
        _
        ) =>
      for {
        argsv  <- tailcall(compileArgs(args))
        bodyv  <- tailcall(compileBodyNonEmpty(body))
      } yield makeLambda(argsv, bodyv, exp.idn)
    case SExpPair(SExpId(Identifier("lambda", _)), _, _) =>
      throw new SchemeCompilerException(s"Invalid Scheme lambda: $exp", exp.idn)
    case SExpPair(
        SExpId(Identifier("if", _)),
        SExpPair(cond, SExpPair(cons, SExpPair(alt, SExpValue(ValueNil, _), _), _), _),
        _
        ) =>
      for {
        condv <- tailcall(this._compile(cond))
        consv <- tailcall(this._compile(cons))
        altv  <- tailcall(this._compile(alt))
      } yield SchemeIf(condv, consv, altv, exp.idn)
    case SExpPair(
        SExpId(Identifier("if", _)),
        SExpPair(cond, SExpPair(cons, SExpValue(ValueNil, _), _), _),
        _
        ) =>
      // Empty else branch is replaced by #f (R5RS states it's unspecified)
      for {
        condv <- tailcall(this._compile(cond))
        consv <- tailcall(this._compile(cons))
      } yield SchemeIf(condv, consv, SchemeValue(ValueBoolean(false), exp.idn), exp.idn)
    case SExpPair(SExpId(Identifier("if", _)), _, _) =>
      throw new SchemeCompilerException(s"Invalid Scheme if: $exp", exp.idn)
    case SExpPair(
        SExpId(Identifier("let", _)),
        SExpPair(SExpId(name), SExpPair(bindings, body, _), _),
        _
        ) =>
      for {
        bindingsv <- tailcall(compileBindings(bindings))
        bodyv     <- tailcall(compileBodyNonEmpty(body))
      } yield SchemeNamedLet(name, bindingsv, bodyv, exp.idn)
    case SExpPair(
        SExpId(Identifier("let", _)),
        SExpPair(bindings, body, _),
        _
        ) =>
      for {
        bindingsv <- tailcall(compileBindings(bindings))
        bodyv     <- tailcall(compileBodyNonEmpty(body))
      } yield SchemeLet(bindingsv, bodyv, exp.idn)
    case SExpPair(SExpId(Identifier("let", _)), _, _) =>
      throw new SchemeCompilerException(s"Invalid Scheme let: $exp", exp.idn)
    case SExpPair(
        SExpId(Identifier("let*", _)),
        SExpPair(bindings, body, _),
        _
        ) =>
      for {
        bindingsv <- tailcall(compileBindings(bindings))
        bodyv     <- tailcall(compileBodyNonEmpty(body))
      } yield SchemeLetStar(bindingsv, bodyv, exp.idn)
    case SExpPair(SExpId(Identifier("let*", _)), _, _) =>
      throw new SchemeCompilerException(s"Invalid Scheme let*: $exp", exp.idn)
    case SExpPair(
        SExpId(Identifier("letrec", _)),
        SExpPair(bindings, body, _),
        _
        ) =>
      for {
        bindingsv <- tailcall(compileBindings(bindings))
        bodyv     <- tailcall(compileBodyNonEmpty(body))
      } yield SchemeLetrec(bindingsv, bodyv, exp.idn)
    case SExpPair(SExpId(Identifier("letrec", _)), _, _) =>
      throw new SchemeCompilerException(s"Invalid Scheme letrec: $exp", exp.idn)
    case SExpPair(
        SExpId(Identifier("set!", _)),
        SExpPair(SExpId(v), SExpPair(value, SExpValue(ValueNil, _), _), _),
        _
        ) =>
      for {
        valuev <- tailcall(this._compile(value))
      } yield SchemeSet(v, valuev, exp.idn)
    case SExpPair(SExpId(Identifier("when", _)), SExpPair(pred, body, _), _) =>
      for {
        predv <- tailcall(this._compile(pred))
        bodyv <- tailcall(compileBodyNonEmpty(body))
      } yield SchemeWhen(predv, bodyv, exp.idn)
    case SExpPair(SExpId(Identifier("when", _)), _, _) =>
      throw new SchemeCompilerException(s"Invalid Scheme when: $exp", exp.idn)
    case SExpPair(SExpId(Identifier("unless", _)), SExpPair(pred, body, _), _) =>
      for {
        predv <- tailcall(this._compile(pred))
        bodyv <- tailcall(compileBodyNonEmpty(body))
      } yield SchemeUnless(predv, bodyv, exp.idn)
    case SExpPair(SExpId(Identifier("unless", _)), _, _) =>
      throw new SchemeCompilerException(s"Invalid Scheme unless: $exp", exp.idn)
    case SExpPair(SExpId(Identifier("set!", _)), _, _) =>
      throw new SchemeCompilerException(s"Invalid Scheme set!: $exp", exp.idn)
    case SExpPair(SExpId(Identifier("begin", _)), body, _) =>
      tailcall(compileBody(body)).map(SchemeBegin(_, exp.idn))
    case SExpPair(SExpId(Identifier("cond", _)), clauses, _) =>
      tailcall(compileCondClauses(clauses)).map(SchemeCond(_, exp.idn))
    case SExpPair(SExpId(Identifier("case", _)), SExpPair(exp, clauses, _), _) =>
      tailcall(compileCaseClauses(clauses)).flatMap({
        case (c, d) => tailcall(this._compile(exp)).map(expv => SchemeCase(expv, c, d, exp.idn))
      })
    case SExpPair(SExpId(Identifier("and", _)), args, _) =>
      tailcall(compileBody(args)).map(SchemeAnd(_, exp.idn))
    case SExpPair(SExpId(Identifier("or", _)), args, _) =>
      tailcall(compileBody(args)).map(SchemeOr(_, exp.idn))
    case SExpPair(
        SExpId(Identifier("define", _)),
        SExpPair(SExpId(name), SExpPair(value, SExpValue(ValueNil, _), _), _),
        _
        ) =>
      tailcall(this._compile(value)).map(SchemeDefineVariable(name, _, exp.idn))
    case SExpPair(
        SExpId(Identifier("define", _)),
        SExpPair(SExpPair(SExpId(name), args, _), body, _),
        _
        ) =>
      for {
        argsv  <- tailcall(compileArgs(args))
        bodyv  <- tailcall(this.compileBodyNonEmpty(body))
      } yield makeDefineFunction(name, argsv, bodyv, exp.idn)
    case SExpPair(
        SExpId(Identifier("do", _)),
        SExpPair(bindings, SExpPair(SExpPair(test, finals, _), commands, _), _),
        _
        ) =>
      for {
        bindingsv <- tailcall(compileDoBindings(bindings))
        testv     <- tailcall(this._compile(test))
        finalsv   <- tailcall(compileBody(finals))
        commandsv <- tailcall(compileBody(commands))
      } yield SchemeDo(bindingsv, testv, finalsv, commandsv, exp.idn)
    case SExpPair(f, args, _) =>
      for {
        fv    <- tailcall(this._compile(f))
        argsv <- tailcall(compileBody(args))
      } yield SchemeFuncall(fv, argsv, exp.idn)
    case SExpId(v) =>
      if (reserved.contains(v.name))  throw new SchemeCompilerException(s"Invalid Scheme identifier (reserved): $exp (${exp.idn.pos})", exp.idn)
      done(SchemeVar(v))
    case SExpValue(value, _)   => done(SchemeValue(value, exp.idn))
  }

  def compileArgs(args: SExp): TailRec[(List[Identifier],Option[Identifier])] = args match {
    case SExpPair(SExpId(id), rest, _) =>
      for {
        restv <- tailcall(compileArgs(rest))
      } yield (id :: restv._1, restv._2)
    case SExpValue(ValueNil, _) => done((Nil,None))
    case SExpId(id)             => done((Nil,Some(id)))
    case _                      => throw new SchemeCompilerException(s"Invalid Scheme argument list: $args", args.idn)
  }

  def compileBodyNonEmpty(body: SExp): TailRec[List[SchemeExp]] = body match {
    case SExpValue(ValueNil, _) => throw new SchemeCompilerException(s"Empty body is not allowed", body.idn)
    case _                      => tailcall(compileBody(body))
  }

  def compileBody(body: SExp): TailRec[List[SchemeExp]] = body match {
    case SExpPair(exp, rest, _) =>
      for {
        expv  <- tailcall(this._compile(exp))
        restv <- tailcall(compileBody(rest))
      } yield expv :: restv
    case SExpValue(ValueNil, _) => done(Nil)
    case _                      => throw new SchemeCompilerException(s"Invalid Scheme body: $body", body.idn)
  }

  def compileBindings(bindings: SExp): TailRec[List[(Identifier, SchemeExp)]] = bindings match {
    case SExpPair(SExpPair(SExpId(v), SExpPair(value, SExpValue(ValueNil, _), _), _), rest, _) =>
      if (reserved.contains(v.name)) throw new SchemeCompilerException(s"Invalid Scheme identifier (reserved): $v", bindings.idn)
      for {
        valuev <- tailcall(this._compile(value))
        restv  <- tailcall(compileBindings(rest))
      } yield (v, valuev) :: restv
    case SExpValue(ValueNil, _) => done(Nil)
    case _                      => throw new SchemeCompilerException(s"Invalid Scheme bindings: $bindings", bindings.idn)
  }

  def compileDoBindings(bindings: SExp): TailRec[List[(Identifier, SchemeExp, Option[SchemeExp])]] =
    bindings match {
      case SExpPair(SExpPair(SExpId(v), SExpPair(value, SExpValue(ValueNil, _), _), _), rest, _) =>
        if (reserved.contains(v.name)) throw new SchemeCompilerException(s"Invalid Scheme identifier (reserved): $v", bindings.idn)
        for {
          valuev <- tailcall(this._compile(value))
          restv  <- tailcall(compileDoBindings(rest))
        } yield (v, valuev, None) :: restv
      case SExpPair(
          SExpPair(SExpId(v), SExpPair(value, SExpPair(step, SExpValue(ValueNil, _), _), _), _),
          rest,
          _
          ) =>
        if (reserved.contains(v.name)) throw new SchemeCompilerException(s"Invalid Scheme identifier (reserved): $v", bindings.idn)
        for {
          valuev <- tailcall(this._compile(value))
          stepv  <- tailcall(this._compile(step))
          restv  <- tailcall(compileDoBindings(rest))
        } yield (v, valuev, Some(stepv)) :: restv
      case SExpValue(ValueNil, _) => done(Nil)
      case _ =>
        throw new SchemeCompilerException(s"Invalid Scheme do-bindings: $bindings", bindings.idn)
    }

  def compileCondClauses(clauses: SExp): TailRec[List[(SchemeExp, List[SchemeExp])]] =
    clauses match {
      case SExpPair(
          SExpPair(SExpId(Identifier("else", _)), body, _),
          SExpValue(ValueNil, _),
          _
          ) =>
        for {
          bodyv  <- tailcall(compileBodyNonEmpty(body))
        } yield List((SchemeValue(ValueBoolean(true), clauses.idn), bodyv))
      case SExpPair(SExpPair(cond, body, _), restClauses, _) =>
        for {
          condv        <- tailcall(this._compile(cond))
          bodyv        <- tailcall(compileBody(body))
          restClausesv <- tailcall(compileCondClauses(restClauses))
        } yield (condv, bodyv) :: restClausesv
      case SExpValue(ValueNil, _) => done(Nil)
      case _ =>
        throw new SchemeCompilerException(s"Invalid Scheme cond clauses: $clauses", clauses.idn)
    }

  def compileCaseClauses(
      clauses: SExp
  ): TailRec[(List[(List[SchemeValue], List[SchemeExp])], List[SchemeExp])] =
    clauses match {
      case SExpPair(
          SExpPair(SExpId(Identifier("else", _)), body, _),
          SExpValue(ValueNil, _),
          _
          ) =>
        for {
          bodyv <- tailcall(compileBodyNonEmpty(body))
        } yield (List(), bodyv)
      case SExpPair(SExpPair(objects, body, _), restClauses, _) =>
        tailcall(compileCaseClauses(restClauses)).flatMap({
          case (compiled, default) =>
            tailcall(compileCaseObjects(objects)).flatMap(
              objectsv =>
                tailcall(compileBodyNonEmpty(body)).map(bodyv => ((objectsv, bodyv) :: compiled, default))
            )
        })
      case SExpValue(ValueNil, _) => done((Nil, Nil))
      case _ =>
        throw new SchemeCompilerException(s"Invalid Scheme case clauses: $clauses", clauses.idn)
    }

  def compileCaseObjects(objects: SExp): TailRec[List[SchemeValue]] = objects match {
    case SExpPair(SExpValue(v, _), rest, _) =>
      for {
        restv <- tailcall(compileCaseObjects(rest))
      } yield SchemeValue(v, objects.idn) :: restv
    case SExpPair(SExpId(id), rest, _) =>
      // identifiers in case expressions are treated as symbols
      for {
        restv <- tailcall(compileCaseObjects(rest))
      } yield SchemeValue(ValueSymbol(id.name), id.idn) :: restv
    case SExpValue(ValueNil, _) => done(Nil)
    case _ =>
      throw new SchemeCompilerException(s"Invalid Scheme case objects: $objects", objects.idn)
  }
  private def makeLambda(args: (List[Identifier],Option[Identifier]),
                         body: List[SchemeExp],
                         idn: Identity) = args._2 match {
    case Some(vararg) => SchemeVarArgLambda(args._1,vararg,body,idn)
    case None         => SchemeLambda(args._1,body,idn)
  }
  private def makeDefineFunction(id: Identifier,
                                 args: (List[Identifier],Option[Identifier]),
                                 body: List[SchemeExp],
                                 idn: Identity) = args._2 match {
    case Some(vararg) => SchemeDefineVarArgFunction(id,args._1,vararg,body,idn)
    case None         => SchemeDefineFunction(id,args._1,body,idn)
  }

  private def expandQuoted(sexp: SExp): TailRec[SchemeExp] = sexp match {
    case sexpVal : SExpValue    => done(value(sexpVal))
    case sexpId : SExpId        => done(value(sexpId))
    case SExpPair(car,cdr,pos)  =>
      for {
        carExp <- tailcall(expandQuoted(car))
        cdrExp <- tailcall(expandQuoted(cdr))
      } yield SchemePair(carExp,cdrExp,pos)
  }

  private def expandQuasiquoted(sexp: SExp, depth: Int): TailRec[SchemeExp] = sexp match {
    // nested quasiquote
    case SExpPair(id@SExpId(Identifier("quasiquote",_)),pair@SExpPair(quasiquoted, nil@SExpValue(ValueNil, _), _),pos) =>
      for {
        qqExp <- expandQuasiquoted(quasiquoted, depth + 1)
      } yield SchemePair(value(id), SchemePair(qqExp, value(nil), pair.idn), pos)
    // unquote
    case SExpPair(id@SExpId(Identifier("unquote",_)),pair@SExpPair(unquoted, nil@SExpValue(ValueNil, _), _),pos) =>
      if (depth == 1) {
        tailcall(this._compile(unquoted))
      } else {
        for {
          uqExp <- expandQuasiquoted(unquoted, depth - 1)
        } yield SchemePair(value(id), SchemePair(uqExp, value(nil), pair.idn), pos)
      }
    // unquote-splicing
    case SExpPair(carp@SExpPair(id@SExpId(Identifier("unquote-splicing",_)),pair@SExpPair(unquotedSpl, nil@SExpValue(ValueNil, _), _),_),cdr,pos) =>
      if (depth == 1) {
        for {
          exp <- tailcall(this._compile(unquotedSpl))
          cdrExp <- tailcall(expandQuasiquoted(cdr, depth))
        } yield SchemeSplicedPair(exp,cdrExp,pos)
      } else {
        for {
          uqExp <- tailcall(expandQuasiquoted(unquotedSpl, depth - 1))
          cdrExp <- tailcall(expandQuasiquoted(cdr, depth))
        } yield SchemePair(SchemePair(value(id), SchemePair(uqExp, value(nil), pair.idn), carp.idn), cdrExp ,pos)
      }
    // throw compiler exceptions on illegal patterns
    case SExpPair(SExpId(Identifier(id,_)), _, _) if Set("quasiquote,unquote,unquote-splicing").contains(id) =>
      throw new SchemeCompilerException(s"Illegal pattern in quasiquote: $sexp", sexp.idn)
    // other s-expressions are expanded as expected
    case sexpId : SExpId        => done(value(sexpId))
    case sexpVal : SExpValue    => done(value(sexpVal))
    case SExpPair(car,cdr,pos)  =>
      for {
        carExp <- tailcall(expandQuasiquoted(car,depth))
        cdrExp <- tailcall(expandQuasiquoted(cdr,depth))
      } yield SchemePair(carExp, cdrExp, pos)
  }

  private def value(sexp: SExpValue): SchemeExp =
    SchemeValue(sexp.value, sexp.idn)
  private def value(sexp: SExpId): SchemeExp =
    SchemeValue(ValueSymbol(sexp.id.name), sexp.id.idn)
}

object SchemeCompiler extends BaseSchemeCompiler