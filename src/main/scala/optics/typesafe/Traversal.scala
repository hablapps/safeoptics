package org.hablapps.gist.optics
package typesafe

import shapeless.{Sized, Nat}

trait Traversal[S, T, A, B]{

  trait Extract[In <: S]{
    type Out <: Result
    def apply(t: In): Out
  }

  object Extract{
    type Aux[In <: S, _Out <: Result] =
      Extract[In]{ type Out = _Out }
  }

  trait Result{
    type N <: Nat
    type OutPut <: T

    def getAll(): Sized[List[A], N]
    def putAll(values: Sized[List[B], N]): OutPut
  }

  object Result{
    type Aux[_N <: Nat, _OutPut <: T] = Result{
      type N = _N
      type OutPut = _OutPut
    }
  }

  def apply[In <: S](t: In)(implicit E: Extract[In]): E.Out = E(t)
}
