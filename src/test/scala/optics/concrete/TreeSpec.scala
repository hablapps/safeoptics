package org.hablapps.gist.optics
package concrete
package test

import org.scalatest._

class TreeSpec extends FunSpec with Matchers{

  val t = Node(Node(Leaf(), 1, Leaf()), 2, Node(Leaf(), 3, Leaf()))

  describe("concrete traversals"){

    val inorder = Tree.InOrderFunList[Int, Int]

    it("should work for getAll"){
      inorder.extract(t).getAll shouldBe List(1, 2, 3)
    }

    it("should work for putAll"){
      inorder.extract(t).putAll(List(4, 5, 6)) shouldBe
        Node(Node(Leaf(), 4, Leaf()), 5, Node(Leaf(), 6, Leaf()))
    }
  }

  describe("van laarhoven traversals"){

    val inorder = Tree.InOrder[Int]

    it("should work for getAll"){
      inorder(Traversal.FunList[Int, Int] _).apply(t).getAll shouldBe List(1, 2, 3)
    }

    it("should work for putAll"){
      inorder(Traversal.FunList[Int, Int] _).apply(t).putAll(List(4, 5, 6)) shouldBe
        Node(Node(Leaf(), 4, Leaf()), 5, Node(Leaf(), 6, Leaf()))
    }
  }
}
