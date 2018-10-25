package scala.tools.escape

import scala.tools.nsc.transform._
import scala.tools.nsc.symtab._
import scala.tools.nsc.plugins._

import scala.language.postfixOps

/**
 * Check that `@safe` symbols do not escape their defining scope.
 */
abstract class EscTransform extends PluginComponent with Transform with
  TypingTransformers with EscUtils {
  // inherits abstract value `global` and class `Phase` from Transform

  import global._                  // the global environment
  import definitions._             // standard classes and methods
  import typer.atOwner             // methods to type trees

  override def description = "Escape check phase"

  /** the following two members override abstract members in Transform */
  val phaseName: String = "escape"

  protected def newTransformer(unit: CompilationUnit): Transformer =
    new EscTransformer(unit)

  class EscTransformer(unit: CompilationUnit) extends TypingTransformer(unit) {

    def dominates(a: Symbol, b: Symbol) =
      b.owner.owner.hasTransOwner(a.owner)
    def dominates(a: Symbol, bs: Set[Symbol]) =
      bs.forall(_.owner.owner.hasTransOwner(a.owner))

    // FIXME: proper sym lookup
    def isSndFun(tpe: Type) = tpe.toString.startsWith("scala.util.escape.->") || tpe.toString.startsWith("->")
    //def isSndSym(s: Symbol) = !isFstSym(s) //s.hasAnnotation(MarkerLocal)
    def isFstSym(s: Symbol): Boolean = symMode(s) <:< FstMode
    def symMode(s:Symbol) =
      s.getAnnotation(MarkerLocal) match {
        case None => FstMode
        case Some(s) => s.atp.typeArgs(0)
      }

    lazy val FstMode = NothingTpe
    lazy val SndMode = AnyTpe
/*
    TODO:

      + check inheritance
      + abstract over mode
      - objects:
          - what is the story for @local this?
          - can one call methods on @local objects?

*/

    // in general: 1st class is more specific than 2nd class
    def traverse(tree: Tree, m: Type, boundary: List[Symbol]): Unit = {
      curTree = tree
      tree match {
      case Literal(x) =>
      case Ident(x) =>
        if (!isFstSym(tree.symbol)) {
          if (!(symMode(tree.symbol) <:< m)) {
            // 2nd class vars are not 1st class
            reporter.error(tree.pos, tree.symbol + " cannot be used as 1st class value @local["+m+"]")
          } else {
            // cannot reach beyond 1st class boundary
            for (b <- boundary) {
              if (!tree.symbol.hasTransOwner(b))
                if (!(symMode(tree.symbol) <:< symMode(b)))
                  reporter.error(tree.pos, tree.symbol + s" cannot be used inside $b")
            }
          }
        }

      case Select(qual, name) =>
        // TODO: is 2nd class ok here?
        traverse(qual,SndMode,boundary)

      case Apply(fun, args) =>
        traverse(fun,SndMode,boundary) // function is always 2nd class
        dprintln(s"--- apply ")

        dprintln(fun.symbol.name)
        dprintln(fun.symbol.owner.name)
        dprintln(fun.symbol.throwsAnnotations.map(_.tpe))



        // find out mode to use for each argument (1st or 2nd)
        val modes = fun.tpe match {
          case mt @ MethodType(params,restpe) =>
            fun match {
              case Apply(TypeApply(Select(qual,name),_),_) => // TBD correct or need to apply type manually?
                params.map(s => symMode(s).asSeenFrom(qual.tpe, fun.symbol.owner))
              case TypeApply(Select(qual,name),_) => // TBD correct or need to apply type manually?
                params.map(s => symMode(s).asSeenFrom(qual.tpe, fun.symbol.owner))
              case Select(qual,name) =>
                params.map(s => symMode(s).asSeenFrom(qual.tpe, fun.symbol.owner))
              case Ident(_) =>
                params.map(s => symMode(s))
              case _ =>
                //println("---> other: "+ fun.getClass + "/"+fun +"/"+fun.symbol.owner)
                params.map(s => symMode(s))
            }
          case _ => Nil
        }
        // check argument expressions according to mode
        // for varargs, assume 1st class (pad to args.length)
        map2(args,modes.padTo(args.length,FstMode))((a,m) => traverse(a,m,boundary))

      case TypeApply(fun, args) =>
        traverse(fun,SndMode,boundary) // function is always 2nd class

      case Assign(lhs, rhs) =>
        // TODO: what if var is @local?
        //traverse(rhs,symMode(tree.symbol),boundary)
        traverse(rhs,FstMode,boundary)

      case If(cond, thenp, elsep) =>
        traverse(cond,SndMode,boundary)
        traverse(thenp,m,boundary)
        traverse(elsep,m,boundary)

      case LabelDef(name, params, rhs) =>
        traverse(rhs,m,boundary)

      case TypeDef(mods, name, tparams, rhs) =>
        traverse(rhs,FstMode,boundary) // 1?

      case ValDef(mods, name, tpt, rhs) =>
        //println(s"--- recurse $m val: ${tree.symbol}")
        traverse(rhs,symMode(tree.symbol),boundary) // need to check if val is 1st or 2nd

      case DefDef(mods, name, tparams, vparamss, tpt, rhs) if tree.symbol.isConstructor =>
        // do nothing

      case DefDef(mods, name, tparams, vparamss, tpt, rhs) =>
        //println(s"--- recurse $m def: ${tree.symbol}")

        // if this def is 1st class, take it as new boundary
        val boundary1 = tree.symbol::boundary
        // function bodies are always 1st class
        traverse(rhs,FstMode,boundary1)

      case Function(vparams, body) =>
        //println(s"--- recurse $m func: ${tree.tpe}")

        // if this def is 1st class, take it as new boundary
        tree.symbol.addAnnotation(newLocalMarker(m))
        val boundary1 = tree.symbol::boundary
        // function bodies are always 1st class
        traverse(body,FstMode,boundary1)


      // Look for SAM closure corresponding to `->`
      // We treat this case specially to make the closure argument @local
      /*
      {
        def apply$body(x: Int): Int = 2.*(x);
        @SerialVersionUID(0) final class $anonfun extends AnyRef with scala.util.escape.->[Int,Int] with Serializable {
          def <init>(): <$anon: Int => Int> = {
            $anonfun.super.<init>();
            ()
          };
          final override <synthetic> def apply(x: Int): Int = apply$body(x)
        };
        new $anonfun()
      }
      */
      case Block(List(
        bd @ DefDef(bmods, bname, tparams, bvparamss, btpt, brhs), /* body */
        cd @ ClassDef(mods, name, params,
          Template(parents, self, List(
            DefDef(_,_,_,_,_,_),   /* <init> */
            DefDef(_,_,_,_,_,_)))) /* <apply> */
        ),
        Apply(Select(New(tpt),_/*<init>*/),_))
        if tpt.symbol == cd.symbol
        && parents.exists(t => isSndFun(t.tpe))
        =>
          // find 2nd class function prototype
          val Some(base) = parents.find(t => isSndFun(t.tpe))

          // extract 'classiness' FIXME: proper sym lookup
          val mode = if (base.tpe.toString.startsWith("scala.util.escape.->*"))
            base.tpe.typeArgs(0) // e.g. `->*`[ReadOnly,File,Int]
          else // `->`
            SndMode

          // add @local annotation to closure parameter
          val List(List(bvparam)) = bvparamss
          bvparam.symbol.addAnnotation(newLocalMarker(mode))

          // if this def is 1st class, take it as new boundary
          bd.symbol.addAnnotation(newLocalMarker(m))
          val boundary1 = bd.symbol::boundary

          // go and check body
          traverse(brhs,FstMode,boundary)


      case Block(stats, expr) =>
        stats.foreach(s => traverse(s,SndMode,boundary))
        traverse(expr,m,boundary)

      case This(qual) => // TODO: ok?

      case TypeTree() => // TODO: what?

      case New(tpt) =>   // TODO: what?

      case Typed(expr, tpt) =>   // TODO: what?
        traverse(expr,m,boundary)

      case EmptyTree =>

      case Super(qual, mix) =>
        traverse(qual,FstMode,boundary) // 1?

      case Throw(expr) =>
        traverse(expr,FstMode,boundary) //

      case Return(expr) =>
        traverse(expr,FstMode,boundary) // escapes

      case Import(expr, selectors) =>
        traverse(expr,FstMode,boundary) // 1?

      case Match(selector, cases) =>
        traverse(selector,FstMode,boundary)
        cases foreach { case cd @ CaseDef(pat, guard, body) =>
          traverse(body,m,boundary)
        }

      case Try(block, catches, finalizer) =>
        traverse(block,m,boundary)
        catches foreach { case cd @ CaseDef(pat, guard, body) =>
          traverse(body,m,boundary)
        }
        traverse(finalizer,m,boundary)

      case ClassDef(mods, name, params, impl) =>
        //println(s"--- recurse $m class: ${tree.symbol}")
        atOwner(tree.symbol) {
          traverse(impl,FstMode,boundary)
        }

      case Template(parents, self, body) =>
        atOwner(currentOwner) {
        // perform a crude RefChecks run:
        // subclasses are only allowed to _add_ @local annotations on
        // method parameters, not to remove them.

        // TODO: what about annotations on members directly,
        // not on method arguments?

            def checkOverride(pair: SymbolPair) = {
              val member   = pair.low
              val other    = pair.high
              def argModes(tpe: Type) = tpe match {
                case mt @ MethodType(params,restpe) => params.map(symMode)
                case _ => Nil
              }
              // member 2, other 1 is OK, but not vice versa
              val memberM = argModes(member.tpe)
              val otherM = argModes(other.tpe)

              def compare(a: Type, b: Type) = {
                val a1 = a.asSeenFrom(pair.rootType,a.typeSymbol.owner)
                val b1 = b.asSeenFrom(pair.rootType,b.typeSymbol.owner)
                val res = a1 <:< b1
                //println(s"$a1 <:<: $b1 = $res")
                res
              }

              val allOK = memberM.length == otherM.length && map2(otherM,memberM)(compare).forall(x=>x)
              if (!allOK) {
                val fullmsg = "overriding " + pair.high.fullLocationString + " with " + pair.low.fullLocationString + ":\n" +
                s"some @local annotations on arguments have been dropped"
                reporter.error(member.pos, fullmsg)
              }
              // require that either both have @local annotation on member or none
              // TODO: what is sensible here?
              if (symMode(member) != symMode(other)) {
                val fullmsg = "overriding " + pair.high.fullLocationString + " with " + pair.low.fullLocationString + ":\n" +
                s"@local annotations on member do not match"
                reporter.error(member.pos, fullmsg)
              }
            }

            val opc = new overridingPairs.Cursor(tree.symbol)
            while (opc.hasNext) {
              if (!opc.high.isClass) checkOverride(opc.currentPair)
              opc.next()
            }

            // now check body (TODO: 2? 1?)
            body.foreach(s => traverse(s,SndMode,boundary))
        }

      case ModuleDef(mods, name, impl) =>
        traverse(impl,FstMode,boundary)

      case PackageDef(pid, stats) =>
        atOwner(tree.symbol) {
          stats.foreach(s => traverse(s,SndMode,boundary))
        }

      case _ =>
        println(s"don't know how to handle ${tree.getClass}")
    }}


    override def transform(tree: Tree): Tree = {
      traverse(tree,FstMode,Nil)
      tree
    }
  }

}
