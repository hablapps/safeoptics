package org.hablapps.gist.optics
package typesafe

trait Affine[S, T, A, B]{

  trait Extract[In <: S]{
    type Out <: Result
    def apply(t: In): Out
  }

  object Extract{
    type Aux[In <: S, _Out <: Result] =
      Extract[In]{ type Out = _Out }
  }

  trait Result{
    type Content[x] <: Option[x]
    type Out <: T
    
    def get(): Content[A]
    def put(value: Content[B]): Out
  }

  object Result{
    type Aux[_Content[x] <: Option[x], _Out <: T] = Result{
      type Content[x] = _Content[x]
      type Out = _Out
    }
  }

  def apply[In <: S](t: In)(implicit E: Extract[In]): E.Out = E(t)
}
