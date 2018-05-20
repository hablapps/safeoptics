package org.hablapps.gist.optics
package concrete
package safe

import org.scalatest._
import shapeless._

class TestNest extends FunSpec with Matchers{

  val n = Cons(1, Cons((2,3), Cons(((4,5),(6,7)), 
    Empty[(((Int,Int),(Int,Int)), ((Int,Int),(Int,Int)))]())))

  Nest.hlist[Int,
    Cons[Int,
      Cons[(Int, Int),
        Cons[((Int, Int), (Int, Int)),
          Empty[(((Int, Int), (Int, Int)), ((Int, Int), (Int, Int)))]]]]](n) shouldBe 
    1 :: (2,3) :: ((4,5),(6,7)) :: HNil
}