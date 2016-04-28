package unif


class UnificationException extends Exception

abstract class Term[A] {
  
   type Subst = Map[LogVar[Any],Term[Any]]
   
   def onUnifies(other: Term[A]) : Boolean
   def unifies(other: Term[A]) : Boolean = {
     mgu(other,Map.empty) match {
       case Some(subst) => 
         other.onUnifies(this)
       case None => false
     }
   }
   def apply(subst: Subst): Term[A] = this
   def onMgu(other: Term[A], subst: Subst) : Option[Subst]
   def mgu(other: Term[A], subst: Subst) : Option[Subst] = other.onMgu(this, subst)
   def mgu(other: Term[A]): Option[Subst] = mgu(other, Map.empty)
   def unify[B](others: UnifCase[A,B]*) : B = {
     for (other <- others) {
       if(other.isInstanceOf[MutUnifCase[A,B]]) {      
         if(unifies(other.pat())) { 
           return other.execute()
         }
       } else {
         mgu(other.pat()) match {
           case Some(subst) => return other.execute(subst) 
           case None => ()
         }         
       }
     }
     
     throw new UnificationException()
   }
   def unifyS[B](subst: Subst, others:PureUnifCase[A,B]*) : B = {
     for (other <- others) {
       mgu(other.pat(), subst) match {
         case Some(nsubst) => return other.execute(subst) 
         case None => ()
       }
     }
     throw new UnificationException()
   }
   def isGround() : Boolean = true
   def >=>[B](body: => B) : MutUnifCase[A,B] = {
      new MutUnifCase[A,B](this, body)
   }
   def withMgu[B](body: Subst => B): PureUnifCase[A,B] = {
      new PureUnifCase[A,B](this, body)
   }
   def isPat(): Boolean = false
}

class NoLogicalInstanceException extends Exception

class LogVar[A]() extends Term[A] {
  private var value: Option[Term[A]] = None
  private var aliases: Set[LogVar[A]] = Set.empty
  def get(): Term[A] = {
    value match {
      case Some(a) => a
      case None    => throw new NoLogicalInstanceException()
    }
  } 
  def set(a: Term[A]) {
    value match {
      case None => {       
         value = Some(a)
         for (alias <- aliases) {
           alias.set(a)
         }
      }
      case _ => ()
    }
  }  
  def retrieve(): Option[Term[A]] = value 
  def retrieve(subst: Subst): Option[Term[A]] = 
    value match {
      case Some(a) => value
      case None => subst.get(this.asInstanceOf[LogVar[Any]]).asInstanceOf[Option[Term[A]]]
    }
  def link(other: LogVar[A]) {
    aliases = aliases + other 
  }
  override def isGround() : Boolean = {
    value match {
      case Some(a) => true
      case _ => false
    }
  }
  def onUnifies(other: Term[A]) : Boolean = {
     if(other.isInstanceOf[LogVar[A]]) {
          val lother = other.asInstanceOf[LogVar[A]]
          (isGround(),lother.isGround()) match {
            case (false,false) => 
              link(lother)
              lother.link(this)
              true
            case (true,false) => 
              lother.set(get())
              true
            case (false,true) => 
              set(lother.get())
              true
            case (true,true) => value.get == lother.get()
          }
     } else {
        if(!isGround()) {
            set(other)
            true
        } else value.get == other
    }
  }
  def onMgu(other: Term[A], subst: Subst) : Option[Subst] = {
     if(other.isInstanceOf[LogVar[A]]) {
         val lother = other.asInstanceOf[LogVar[Any]]
         (retrieve(subst),lother.retrieve(subst)) match {
           case (None,None) => Some(subst + (this.asInstanceOf[LogVar[Any]] -> other.asInstanceOf[Term[Any]]))
           case (None,Some(u)) => Some(subst + (this.asInstanceOf[LogVar[Any]] -> u))
           case (Some(v),None) => Some(subst + (this.asInstanceOf[LogVar[Any]] -> v.asInstanceOf[Term[Any]]))
           case (Some(v),Some(u)) => if (v == u) Some(subst) else None
         }
     } else {
       retrieve(subst) match {
          case Some(v) => if (v == other) Some(subst) else None
          case None => Some(subst + (this.asInstanceOf[LogVar[Any]] -> other.asInstanceOf[Term[Any]]))
       }
     }
  }
  override def apply(subst: Subst): Term[A] = {
    if (isGround()) {
      value.get
    } else {
      subst.get(this.asInstanceOf[LogVar[Any]]) match {
        case Some(t) => t.asInstanceOf[Term[A]]
        case _ => this
      }
    }
  }
  override def toString() : String = {
    value match {
      case Some(a) => a.toString() 
      case None    => "var-" + hashCode()
    }
  }
  override def equals(other: Any) : Boolean = {
    if (other.isInstanceOf[LogVar[A]]) {
      val lother = other.asInstanceOf[LogVar[A]]
      if(isGround() && lother.isGround()) {
        // println("eq-ed")
        // println(value.get)
        // println(lother.get())
        value.get == lother.get()
      } else hashCode() == lother.hashCode()
    } else this.hashCode() == other.hashCode()
  }

}


case class Const[A](n: A) extends Term[A] {
  def get() : Any = n
  def onUnifies(other: Term[A]) : Boolean = {
    other match {
      case Const(m) => m == n
      case _ =>
        if(other.isInstanceOf[LogVar[A]]) {
          val lother = other.asInstanceOf[LogVar[A]]
          if(lother.isGround()) {
             lother.get() == this
          } else {
             lother.set(this)
             true
          }
        } else false
    }
  }
  def onMgu(other: Term[A], subst:Subst): Option[Subst] = {
    other match {
      case Const(m) => Some(subst)
      case _ =>
        if(other.isInstanceOf[LogVar[A]]) {
          val lother = other.asInstanceOf[LogVar[A]]
          lother.retrieve(subst) match {
            case Some(v) => if(v == this) Some(subst) else None
            case None => Some(subst + (lother.asInstanceOf[LogVar[Any]] -> this.asInstanceOf[Term[Any]]))
          }
        } else None
    }
  }
  override def toString() : String = "const(" + n.toString() + ")"
  override def equals(other: Any): Boolean = {
    // println("Ran const eq")
    if(other.isInstanceOf[Term[A]]) {
      this.hashCode() == other.hashCode()
    } else false
  }
  override def hashCode(): Int = {
    // println("Ran const hash")
    n.hashCode()
  }
}


case class Func[A](sym: String, args: List[Term[Any]]) extends Term[A] {
   
   override def isGround(): Boolean = {
     val ls = args.map( _.isGround() )
     ls.foldLeft(true)(_ && _)
   }
   override def onUnifies(other: Term[A]) : Boolean = {
     other match {
       case Func(s,as) => 
         if(s == sym && args.length == as.length) {
           var curr: Boolean = true
           for ((arg:Term[Any],a:Term[Any]) <- args.zip(as)) {
             if (curr) curr = arg.onUnifies(a) else return false
           }
           return curr
         } else {
           false
         }
       case _ =>
         if(other.isInstanceOf[LogVar[A]]) {
           val lother = other.asInstanceOf[LogVar[A]]
           if(lother.isGround()) {
             onUnifies( lother.get() ) 
           } else {
             lother.set(this)
             true
           }
         } else false
     }
   }   
   override def onMgu(other: Term[A], subst: Subst) : Option[Subst] = {
     other match {
       case Func(s,as) =>
         if (sym == s && args.length == as.length) {
           var curr: Option[Subst] = Some(subst)
           for ((arg:Term[Any],a:Term[Any]) <- args.zip(as)) {
             curr match {
               case Some(st) => 
                 curr = arg.onMgu(a,st)
               case None => return None
             }
           }
           return curr
         } else None 
       case _ =>
         if(other.isInstanceOf[LogVar[A]]) {
           val lother = other.asInstanceOf[LogVar[A]]
           lother.retrieve(subst) match {
             case Some(f) => onMgu(f, subst)
             case None    => Some(subst + (lother.asInstanceOf[LogVar[Any]] -> this.asInstanceOf[Term[Any]]))
           }
         } else None
     }
   }
   override def apply(subst: Subst): Term[A] = {
     var ls: List[Term[Any]] = List()
     for (arg <- args) {
       ls = ls :+ arg.apply(subst)       
     }
     Func(sym,ls)
   }
   override def toString(): String = {
     sym + "(" + args.map( _.toString() ).mkString(",") + ")" 
   }
}

abstract class UnifCase[A,B](pat: Term[A]) {
  type Subst = Map[LogVar[Any],Term[Any]]  
  def pat(): Term[A] = pat
  def execute(subst: Subst): B 
  def execute(): B = execute(Map.empty)
  override def toString(): String = {
    pat.toString() + "==> <body>" 
  }
}

class MutUnifCase[A,B](pat: Term[A], body: => B) extends UnifCase[A,B](pat) {
  override def execute(subst: Subst): B = body
}

class PureUnifCase[A,B](pat: Term[A], body:  Map[LogVar[Any],Term[Any]] => B) extends UnifCase[A,B](pat) {
  override def execute(subst: Subst): B = body(subst)
}

case class Unif[A](pat: Term[A]) {
  type Subst = Map[LogVar[Any],Term[Any]]  
  def unapply(t: Term[A]): Option[Subst] = {
    t.mgu(pat, Map.empty)
  }
}

object Twice {
  def unapply(x: Int): Option[Int] = if(x%2==0) Some(x/2) else None
  def test(x: Int) {
    x match {
      case Twice(y) => println(x + "is even and twice of " + y)
      case _ => println(x + " is odd")
    }
  }
}
