package org.hablapps.gist.optics
package concrete
package test

sealed abstract class Tree[A]
case class Leaf[A]() extends Tree[A]
case class Node[A](left: Tree[A], root: A, right: Tree[A]) extends Tree[A]

object Tree{

  object Syntax{
    def leaf[A](): Tree[A] = Leaf[A]()
    def node[A](l: Tree[A], a: A, r: Tree[A]): Tree[A] = Node(l,a,r)
  }

  // VANLAARHOVEN

  import scalaz.Applicative, scalaz.syntax.applicative._

  implicit def InOrder[A] = new vanLaarhoven.Traversal[Tree[A],A]{
    def apply[F[_]: Applicative](f: A => F[A]): Tree[A] => F[Tree[A]] = {
      case Leaf() => (Leaf[A](): Tree[A]).point[F]
      case Node(left, root, right) =>
        (apply[F](f).apply(left) |@| f(root) |@| apply[F](f).apply(right))(
          (fl,fa,fr) => Node(fl,fa,fr)
        )
    }
  }

  // FUNLIST

  import Traversal.{Done, More, FunList}

  implicit def InOrderFunList[A, B] = new Traversal[Tree[A], Tree[B], A, B]{
    def extract(s: Tree[A]): FunList[A, B, Tree[B]] = s match {
      case Leaf() => Done(Leaf())
      case Node(left, root, right) =>
        (extract(left) |@|
          FunList[A, B](root) |@|
          extract(right))(Node.apply)
    }
  }
}
