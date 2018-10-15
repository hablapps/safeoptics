// package org.hablapps.gist.optics
// package concrete
// package safe

// import org.scalatest._
// import shapeless._

// class TestOdd extends FunSpec with Matchers{

//   import typesafe.{List,::,Nil}
//   import Traversal.{More,Done}

//   val Content = new Content[Int,String]
//   import Content._

//   val l2: ::[Int, ::[Int, ::[Int, ::[Int, Nil[Int]]]]] =
//     ::(1, ::(2, ::(3, ::(4, Nil[Int]()))))

//   type StringList4 = String :: String :: String :: String :: Nil[String]

//   val fl:
//     More[Int, String, StringList4,
//       More[Int, String, String => StringList4,
//         Done[Int, String, String => String => StringList4]]] =
//     More(1,
//       More(2,
//         Done(s1 => s2 => ::(s1, ::("2", ::(s2, ::("4", Nil[String]())))))))

//   val fl0: Done[Int,String,Nil[String]] = ???

//   val fl1: More[Int,String,Boolean::Nil[String],
//     Done[Int,String,String=>Boolean::Nil[String]]] = addOneMore(fl0)

//   val fl2: More[Int,String,Boolean::Boolean::Nil[String],
//     More[Int,String,String => Boolean::Boolean::Nil[String],
//       Done[Int,String,String => String => Boolean::Boolean::Nil[String]]]] = addOneMore(fl1)

//   val fl3: More[Int,String,Boolean::Boolean::Boolean::Nil[String],
//     More[Int,String,String => Boolean::Boolean::Boolean::Nil[String],
//       More[Int,String,String => String => Boolean::Boolean::Boolean::Nil[String],
//         Done[Int,String,String => String => String => Boolean::Boolean::Boolean::Nil[String]]]]] = addOneMore(fl1)

//   // val l0 = Nil[Int]()
//   // val l1 = ::(1, Nil[Int]())

//   // Content(l0) shouldBe 1
//   // Content(l1)(consContent[Nil[Int],
//   //   Done[Int,String,String=>(String :: Nil[String])]]) shouldBe 1

//   // val Odds = new Odds[Int,String]
//   // import Odds._

//   // val l0 = Nil[Int]()
//   // val l1 = ::(1, Nil[Int]())
//   // val l2 = ::(1, ::(2, Nil[Int]()))

//   // Odds(l0) shouldBe 1
//   // Odds(l1) shouldBe 1
//   // Odds(l2)(consOdds[Nil[Int],
//   //   More[Int,String,String=>Nil[String],
//   //     Done[Int,String,String => String => Nil[String]]]](
//   //       ??? /*nilOdds*/)) shouldBe 1

// }
