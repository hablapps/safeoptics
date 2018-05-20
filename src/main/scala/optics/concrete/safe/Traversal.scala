package org.hablapps.gist.optics
package concrete
package safe

import typesafe.{List, Nil, ::}
import Traversal._

trait Traversal[S,T,A,B]{
  
  def apply[In <: S](s: In)(implicit E: Extract[S,T,A,B,In]): E.Out = 
    E(s)

  def getAll[In <: S, O <: T, FL <: FunList[A,B,O], L <: List[A]](s: In)(implicit 
    E: Extract.Aux[S,T,A,B,In,O,FL],
    G: Get.Aux[A,B,O,FL,L]): G.Out = 
    G(E(s))
}

object Traversal{

  // EXTRACT

  trait Extract[S,T,A,B,In <: S]{
    type O <: T
    type Out <: Traversal.FunList[A,B,O]
    def apply(s: In): Out
  }

  object Extract{
    type Aux[S,T,A,B,In <: S, _O <: T, _Out <: Traversal.FunList[A,B,_O]] = 
      Extract[S,T,A,B,In]{
        type O = _O
        type Out = _Out
      }
  }

  // FUNLIST 

  sealed abstract class FunList[A,B,T]
  case class Done[A,B,T](t: T) extends FunList[A,B,T]
  case class More[A,B,T,FL <: FunList[A,B,B=>T]](
    a: A, f: FL) extends FunList[A,B,T]

  // ADD ONE MORE

  trait AddOneMore[A,B,T1,FL<:FunList[A,B,T1]]{
    type T2
    type Out <: More[A,B,FunList[A,B,B=>T2]
    def apply(in: FL)(a: A, update: (B, T1) => 
  }

  // GET 

  trait Get[A,B,O, In <: FunList[A,B,O]]{
    type Out <: List[A]
    def apply(fl: In): Out
  }

  object Get{
    type Aux[A,B,O,FL <: FunList[A,B,O],_Out <: List[A]] = Get[A,B,O,FL]{
      type Out = _Out 
    }

    implicit def doneGet[A,B,O] = new Get[A,B,O,Done[A,B,O]]{
      type Out = Nil[A]
      def apply(fl: Done[A,B,O]) = Nil[A]()
    }

    implicit def moreGet[A,B,O,FL <: FunList[A,B,B=>O]](implicit 
      G: Get[A,B,B=>O,FL]) = new Get[A,B,O,More[A,B,O,FL]]{
      type Out = A :: G.Out
      def apply(fl: More[A,B,O,FL]) = ::(fl.a, G(fl.f))
    }
  }

  // PUT 

  trait Put[A,B,O, In <: FunList[A,B,O]]{
    type Out <: List[B]
    def apply(fl: In): Out => O
  }

  object Put{
    type Aux[A,B,O,FL <: FunList[A,B,O],_Out <: List[B]] = Put[A,B,O,FL]{
      type Out = _Out 
    }

    implicit def donePut[A,B,O] = new Put[A,B,O,Done[A,B,O]]{
      type Out = Nil[B]
      def apply(fl: Done[A,B,O]) = _ => fl.t
    }

    implicit def morePut[A,B,O,FL <: FunList[A,B,B=>O]](implicit 
      P: Put[A,B,B=>O,FL]) = new Put[A,B,O,More[A,B,O,FL]]{
      type Out = B :: P.Out
      def apply(fl: More[A,B,O,FL]) = bs => 
        P(fl.f)(bs.tail)(bs.head)
    }
  }

}