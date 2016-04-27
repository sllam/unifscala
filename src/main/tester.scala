package main

import unif.Term
import unif.Const
import unif.LogVar
import unif.Func
import unif.Unif

object tester {

  class S(arg1:Term[Int], arg2:Term[Int]) extends Func[Int]("S", List(arg1.asInstanceOf[Term[Any]],arg2.asInstanceOf[Term[Any]]))
  
  def main(args: Array[String]) {
    println("Testing!")
    
    val a = new LogVar[Int]()
    val b = new LogVar[Int]() 
    val c = new LogVar[Int]()
    val d = new LogVar[Int]()
    val e = Const(10)
    
    
    a match {
      case `b` => println("Funny")
      case _ => println("Hooray!")
    }
    
    
    println(a.equals(b))
    println(a == b)    
    
    a.unifies(b)
    a.unifies(c)
    c.unifies(d)
    e.unifies(d)
    println(a + " " + b + " " + c + " " + d)
    
    val f = Const(10)
    println(f == e)
    println(a.equals(b))
    println(a == b)    
    println(Const(10) == Const(10))
    
    println(new S(a,b))
    
    val x = new LogVar[Int]()
    val y = new LogVar[Int]()
    val g1 = new S(x,x)
    val g2 = new S(y,Const(20))
    // g1.unify(g2)
    // println(g1 + " " + g2)
    // println(x == y)
    
    g1 unify[Unit] (
       Const(4) withMgu (theta => {
         println("Wrong!")
       }),
       g2 >=> {
         println("Done! " + x + y)
       }
    )
    
    
    val r = new LogVar[Int]()
    val four = Const(4)
    val unif = Unif[Int](Const(4))
    r match {
      case unif(theta)  => println(theta)
    }
    
    val q = new LogVar[Int]()
    val unifQ = Unif(q)
    Const(4) match {
      case unifQ(theta) => println(theta)
    }
    
  }
  
  def testit(fn: Function[Int,Any]*) {
     fn.foreach(f => println(f(2)))
  }
  
}