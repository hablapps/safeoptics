package org.hablapps.gist.optics
package typesafe

sealed abstract class Tree[A]
case class Leaf[A]() extends Tree[A]
case class Node[T1 <: Tree[A], A, T2 <: Tree[A]](
  left: T1, root: A, right: T2) extends Tree[A]

object Tree{

  class Of[A,B]{
    import shapeless.{Sized, Nat, Succ, _0}
    import shapeless.syntax.sized._
    import shapeless.ops.nat.{ToInt, Diff, Sum}

    implicit object InOrder extends typesafe.Traversal[Tree[A],Tree[B],A,B]{

      implicit val leafInOrder = new Extract[Leaf[A]]{
        type Out = Result.Aux[_0, Leaf[B]]

        def apply(tree: Leaf[A]) = new Result{
          type N = _0
          type OutPut = Leaf[B]

          def getAll() = Sized[List]()
          def putAll(nil: Sized[List[B], _0]) = Leaf[B]()
        }
      }

      implicit def nodeInOrder[
        L <: Tree[A], L_N <: Nat, L_Out <: Tree[B],
        R <: Tree[A], R_N <: Nat, R_Out <: Tree[B],
        _N <: Nat](implicit
        extractL: Extract.Aux[L, Result.Aux[L_N, L_Out]],
        extractR: Extract.Aux[R, Result.Aux[R_N, R_Out]],
        S: Sum.Aux[L_N, Succ[R_N], _N],
        D: Diff.Aux[_N, L_N, Succ[R_N]],
        TI: ToInt[L_N]) =

        new Extract[Node[L,A,R]]{
          type Out = Result.Aux[_N, Node[L_Out, B, R_Out]]

          def apply(tree: Node[L, A, R]) = new Result{
            type N = _N
            type OutPut = Node[L_Out, B, R_Out]

            def getAll() =
              extractL(tree.left).getAll ++
                (tree.root +: extractR(tree.right).getAll)

            def putAll(content: Sized[List[B], N]) =
              content.splitAt[L_N] match {
                case (ll, rl) =>
                  Node(extractL(tree.left).putAll(ll), rl.head,
                    extractR(tree.right).putAll(rl.tail))
              }
          }
        }
    }
  }

  object Monomorphic{
    def apply[A]: Of[A,A] = new Of[A,A]
  }

  object Polymorphic{
    def apply[A,B]: Of[A,B] = new Of[A,B]
  }
}

