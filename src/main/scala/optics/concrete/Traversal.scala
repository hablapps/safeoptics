package org.hablapps.gist.optics
package concrete

trait Traversal[S,T,A,B]{
  def extract(s: S): Traversal.FunList[A,B,T]
}

object Traversal{

  sealed abstract class FunList[A,B,T]
  case class Done[A,B,T](t: T) extends FunList[A,B,T]
  case class More[A,B,T](a: A, f: FunList[A,B,B => T]) extends FunList[A,B,T]

  object FunList{
    implicit class FunListOps[A,B,T](f: FunList[A,B,T]){
      def getAll(): List[A] = f match {
        case Done(_) => List()
        case More(a,f) => a::f.getAll
      }

      def putAll(l: List[B]): T = ((l,f) : @unchecked) match {
        case (Nil, Done(t)) => t
        case (head :: tail, More(_, flb)) => flb.putAll(tail)(head)
        // otherwise, undefined
      }

    }

    def apply[A, B](a: A): FunList[A, B, B] = More(a, Done(identity[B]))

    import scalaz.Functor

    implicit def FunctorFunList[A, B] = new Functor[FunList[A, B, ?]]{
      def map[S, T](fs: FunList[A, B, S])(f: S => T): FunList[A, B, T] =
        fs match {
          case Done(s) => Done(f(s))
          case More(a, fl) => More(a, map(fl)(_ andThen f))
        }
    }

    import scalaz.Applicative, scalaz.syntax.functor._

    implicit def ApplicativeFunList[A, B] = new Applicative[FunList[A, B, ?]]{
      def point[T](t: => T) = Done(t)
      def ap[S, T](fs: => FunList[A, B, S])(
          fst: => FunList[A, B, S => T]): FunList[A, B, T] =
        fst match {
          case Done(st) =>
            fs map st
          case More(a, flbst) =>
            More(a, ap(fs)(flbst map (fsbt => (s: S) => (b: B) => fsbt(b)(s))))
        }
    }

    import scalaz.Comonad

    def funListComonad[A] = new Comonad[FunList[A, A, ?]]{

      def map[S, T](store: FunList[A, A, S])(f: S => T): FunList[A, A, T] =
        store map f

      def duplicate[S](store: FunList[A, A, S]): FunList[A, A, FunList[A, A, S]] =
        store match {
          case Done(s) =>
            Done[A, A, FunList[A, A, S]](Done(s))
          case More(a, flas) =>
            More(a, duplicate(flas) map { f: FunList[A, A, A => S] =>
              ((a: A) => f map (fas => fas(a))): (A => FunList[A, A, S])
            })
        }

      def cobind[S, T](store: FunList[A, A, S])(f: FunList[A, A, S] => T): FunList[A, A, T] =
        store match {
          case Done(s) =>
            Done[A, A, T](f(Done(s)))
          case More(a, flas) =>
            More(a, cobind(flas){ g: FunList[A, A, A => S] =>
              ((a: A) => f(g map (f => f(a)))) : (A => T)
            })
        }

      def copoint[S](store: FunList[A, A, S]): S =
        store match {
          case Done(s) => s
          case More(a, fl) => copoint(fl)(a)
        }
    }
  }


  trait Laws[S,T,A,B]{
    val T: Traversal[S,T,A,B]

    // Precondition: b.length == T.extract(s).getAll.length
    def putget(s: S, b: List[B]): Boolean
    def getput(s: S): Boolean
    def putput(s: S, b1: List[B], b2: List[B]): Boolean
  }
}
