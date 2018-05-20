package org.hablapps.gist.optics
package concrete
package safe

import typesafe.{List,::,Nil}
import Traversal._

class Content[A,B] extends safe.Traversal[List[A],List[B],A,B]{

  implicit val nilContent = new Extract[List[A],List[B],A,B,Nil[A]]{
    type O = Nil[B]
    type Out = Done[A,B,Nil[B]]
    def apply(list: Nil[A]) = Done(Nil[B]())
  }

  trait AsFunction[B,T]{
    type Out
  }

  object AsFunction{
    implicit def just[B,T] = new AsFunction[B,T]{
      type Out = T
    }

    implicit def more[B,T](implicit as: AsFunction[B,T]) =
      new AsFunction[B,B=>T]{
        type Out = as.Out
      }
  }

  implicit def consContent[
      LA <: List[A], 
      LB <: List[B], 
      O,
      FL <: FunList[A,B,O],
      FL2 <: FunList[A,B,B=>B::LB]](implicit
      As: AsFunction[B,O,LB],
      E: Extract.Aux[List[A],List[B],A,B,LA,O,FL]) = 
    new Extract[List[A], List[B], A, B, A :: LA]{
      type O = B :: LB
      type Out = More[A, B, B :: LB,FL2]
      def apply(list: A :: LA) =  
        ??? // More(list.head, E(list.tail))
    }
}

// class Odds[A,B] extends safe.Traversal[List[A],List[B],A,B]{

//   implicit val nilOdds = new Extract[List[A],List[B],A,B,Nil[A]]{
//     type Out = Done[A,B,List[B]]
//     def apply(list: Nil[A]) = Done(Nil[B]())
//   }

//   implicit val oneElementOdds = new Extract[List[A],List[B],A,B,A :: Nil[A]]{
//     type Out = More[A,B,List[B],Done[A,B,B=>List[B]]]
//     def apply(list: A :: Nil[A]) = 
//       More(list.head, Done(::(_, Nil[B])))
//   }

//   implicit def consOdds[LL <: List[A], FL <: FunList[A,B,B=>List[B]]](implicit
//       E: Extract.Aux[List[A],B=>List[B],A,B,LL,FL]) = 
//     new Extract[List[A], List[B], A, B, A :: A :: LL]{
//       type Out = More[A,B,List[B],FL]
//       def apply(list: A :: A :: LL) =  
//         More(list.head, E(list.tail.tail))
//     }
// }
