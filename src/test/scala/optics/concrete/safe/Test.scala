package org.hablapps.gist
package optics
package concrete
package safe

import org.scalatest._
import typesafe.{Tree,Node,Leaf,Nil,::}

class Test extends FunSpec with Matchers{

  describe("Polymorphic traversals"){

    val TreeOfIntString = Tree.Polymorphic[Int,String]
    import TreeOfIntString.InOrder

    it("should allow us to get all the integers"){
      val in: Node[Node[Leaf[Int],Int,Leaf[Int]], Int, Node[Leaf[Int],Int,Leaf[Int]]] =
        Node(Node(Leaf[Int](),1,Leaf[Int]()), 2, Node(Leaf[Int](),3,Leaf[Int]()))

      InOrder(in).getAll shouldBe ::(1, ::(2, ::(3, Nil[Int]())))
    }

    it("should allow us to change the content and its type"){
      val in: Node[Node[Leaf[Int],Int,Leaf[Int]], Int, Node[Leaf[Int],Int,Leaf[Int]]] =
        Node(Node(Leaf[Int](),1,Leaf[Int]()), 2, Node(Leaf[Int](),3,Leaf[Int]()))

      val out: Node[Node[Leaf[String],String,Leaf[String]], String, Node[Leaf[String],String,Leaf[String]]] =
        InOrder(in).putAll(::("3",::("4",::("5",Nil[String]()))))

      out shouldBe
        Node(Node(Leaf[String](),"3",Leaf[String]()), "4", Node(Leaf[String](),"5",Leaf[String]()))
    }
  }
}