package org.hablapps.gist
package optics
package typesafe

import org.scalatest._
import shapeless._, nat._, ops.nat._

class TestSized extends FunSpec with Matchers{

  describe("Monomorphic traversals"){

    val TreeOfInt = Tree.Monomorphic[Int]
    import TreeOfInt.InOrder

    describe("GetAll for InOrder traversals"){

      it("should return empty list for empty trees"){
        val content: Sized[List[Int], _0] =
          InOrder(Leaf[Int]()).getAll

        content shouldBe Sized[List]()
      }

      it("should return non-nempty lists for non-empty trees"){
        val content: Sized[List[Int], _3] =
          InOrder(Node(Node(Leaf[Int](),1,Leaf[Int]()), 2, Node(Leaf[Int](),3,Leaf[Int]())))
            .getAll

        content shouldBe Sized[List](1, 2, 3)
      }

      it("should not compile when size expectations are wrong"){
        """val content1: Sized[List[Int], _1] =
          InOrder(Leaf[Int]()).getAll""" shouldNot compile

        """val content2: Sized[List[Int], _2] =
             InOrder(Node(Node(Leaf[Int](),1,Leaf[Int]()), 2, Node(Leaf[Int](),3,Leaf[Int]())))
               .getAll""" shouldNot compile
      }
    }

    describe("PutAll for InOrder traversals"){

      it("should return the empty tree for updates of empty trees"){
        val out: Leaf[Int] =
          InOrder(Leaf[Int]()).putAll(Sized[List]())

        out shouldBe Leaf()
      }

      it("should return an updated tree for updates on non-empty trees"){
        val in: Node[Node[Leaf[Int],Int,Leaf[Int]], Int, Node[Leaf[Int],Int,Leaf[Int]]] =
          Node(Node(Leaf[Int](),1,Leaf[Int]()), 2, Node(Leaf[Int](),3,Leaf[Int]()))

        val out: Node[Node[Leaf[Int],Int,Leaf[Int]], Int, Node[Leaf[Int],Int,Leaf[Int]]] =
          InOrder(in).putAll(Sized[List](3, 4, 5))

        out shouldBe
          Node(Node(Leaf[Int](),3,Leaf[Int]()), 4, Node(Leaf[Int](),5,Leaf[Int]()))
      }

      it("should not compile when input size expectations are wrong"){
        """InOrder(Leaf[Int]()).putAll(Sized[List](1))""" shouldNot compile

        """InOrder(Node(Node(Leaf[Int](),1,Leaf[Int]()), 2, Node(Leaf[Int](),3,Leaf[Int]())))
          .putAll(Sized[List](4, 5))""" shouldNot compile

        """InOrder(Node(Node(Leaf[Int](),1,Leaf[Int]()), 2, Node(Leaf[Int](),3,Leaf[Int]())))
          .putAll(Sized[List](2, 3, 4, 5))""" shouldNot compile
      }

      it("should not compile when output size expectations are wrong"){
        """val out: Node[Leaf[Int],Int,Leaf[Int]] = InOrder(Leaf[Int]()).putAll(Nil[Int]())""" shouldNot compile

        """val out: Node[Leaf[Int], Int, Node[Leaf[Int],Int,Leaf[Int]]] =
          InOrder(Node(Node(Leaf[Int](),1,Leaf[Int]()), 2, Node(Leaf[Int](),3,Leaf[Int]())))
            .putAll(Sized[List](3, 4, 5))""" shouldNot compile
      }
    }
  }

  describe("Polymorphic traversals"){

    val TreeOfIntString = Tree.Polymorphic[Int,String]
    import TreeOfIntString.InOrder

    it("should allow us to get all the integers"){
      val in: Node[Node[Leaf[Int],Int,Leaf[Int]], Int, Node[Leaf[Int],Int,Leaf[Int]]] =
        Node(Node(Leaf[Int](),1,Leaf[Int]()), 2, Node(Leaf[Int](),3,Leaf[Int]()))

      InOrder(in).getAll shouldBe Sized[List](1, 2, 3)
    }

    it("should allow us to change the content and its type"){
      val in: Node[Node[Leaf[Int],Int,Leaf[Int]], Int, Node[Leaf[Int],Int,Leaf[Int]]] =
        Node(Node(Leaf[Int](),1,Leaf[Int]()), 2, Node(Leaf[Int](),3,Leaf[Int]()))

      val out: Node[Node[Leaf[String],String,Leaf[String]], String, Node[Leaf[String],String,Leaf[String]]] =
        InOrder(in).putAll(Sized[List]("3", "4", "5"))

      out shouldBe
        Node(Node(Leaf[String](),"3",Leaf[String]()), "4", Node(Leaf[String](),"5",Leaf[String]()))
    }
  }
}
