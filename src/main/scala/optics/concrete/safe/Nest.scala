package org.hablapps.gist.optics
package concrete
package safe

sealed abstract class Nest[A]
case class Empty[A]() extends Nest[A]
case class Cons[A, N<:Nest[(A,A)]](head: A, tail: N) extends Nest[A]

object Nest{
  import shapeless._

  def hlist[A, N <: Nest[A]](in: N)(implicit H: ToHList[A,N]) = H(in)

  trait ToHList[A, In <: Nest[A]]{
    type Out <: HList
    def apply(in: In): Out
  }

  object ToHList{
    implicit def nil[A] = new ToHList[A, Empty[A]]{
      type Out = HNil
      def apply(in: Empty[A]) = HNil
    }

    implicit def cons[A,L<:Nest[(A,A)]](implicit
      L: ToHList[(A,A), L]) = new ToHList[A, Cons[A, L]]{
      type Out = A :: L.Out
      def apply(in: Cons[A, L]) = in.head :: L(in.tail)
    }
  }
}

