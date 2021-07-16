package maf.core

import maf.util.SmartHash
import scala.annotation.tailrec
import maf.lattice.interfaces.LatticeWithAddrs
import maf.modular.scheme.VarAddr
import maf.modular.scheme.PtrAddr

case class UnboundAddress[A <: Address](a: A) extends Error

trait Store[A <: Address, V] extends SmartHash { store =>
  // This type is the specific subtype of store that `this` belongs to
  type This >: this.type <: Store[A, V] { type This = store.This }
  /** Looks up a value in the store */
  def lookup(a: A): Option[V]
  /** Add a new entry in the store */
  def extend(a: A, v: V): This
  // Derived operations
  def apply(a: A): V = lookup(a).get
  def lookupDefault(a: A, default: V): V = lookup(a) match {
    case Some(a) => a
    case None    => default
  }
  def lookupMF(a: A): MayFail[V, Error] = lookup(a) match {
    case Some(a) => MayFail.success(a)
    case None    => MayFail.failure(UnboundAddress(a))
  }
  /** Update (strong update if possible) an entry in the store */
  def update(a: A, v: V): This = extend(a, v)
  /** Tries to update an address if it's already mapped into the store. Otherwise, extend the store */
  def updateOrExtend(a: A, v: V): This = extend(a, v)
  /** Join with another store */
  def empty: This 
  def join(other: This): This 
}

//
// STANDARD MAP-BASED STORE
//

case class BasicStore[A <: Address, V: Lattice](content: Map[A,V]) extends Store[A, V] { outer =>
  // refine the This type
  type This = BasicStore[A, V]
  // lookup
  def lookup(a: A): Option[V] = content.get(a)
  // extend
  def extend(a: A, v: V): This = extendOption(a, v).getOrElse(this)
  def extendOption(a: A, v: V): Option[This] = lookup(a) match {
    case None if Lattice[V].isBottom(v) => None
    case None => Some(BasicStore(content + (a -> v)))
    case Some(oldValue) =>
      val newValue = Lattice[V].join(oldValue, v)
      if (oldValue == newValue) {
        None
      } else {
        Some(BasicStore(content + (a -> newValue)))
      }
    }
  // join
  def empty = BasicStore(Map.empty)
  def join(other: BasicStore[A,V]): BasicStore[A,V] =
    BasicStore(other.content.foldLeft(content) { case (acc, (adr, vlu)) => 
      acc.get(adr) match {
        case None => acc + (adr -> vlu)
        case Some(accVlu) => acc + (adr -> Lattice[V].join(accVlu, vlu))
      }
    })
}

//
// LOCAL STORE, WHICH SUPPORTS ABSTRACT GC AND ABSTRACT COUNTING
//

sealed trait AbstractCount { 
  def inc: AbstractCount
  def join(other: AbstractCount): AbstractCount
}
case object CountOne extends AbstractCount { 
  def inc = CountInf
  def join(other: AbstractCount) = other
}
case object CountInf extends AbstractCount { 
  def inc = CountInf
  def join(other: AbstractCount) = this
}

case class LocalStore[A <: Address, V](content: Map[A, (V, Set[A], AbstractCount)])(implicit val lattice: LatticeWithAddrs[V, A]) 
  extends Store[A, V] { outer =>
  // refine the This type
  type This = LocalStore[A, V]
  // lookup
  def lookup(a: A): Option[V] = content.get(a).map(_._1)
  // allow to disable abstract counting for certain addresses
  def freshCountFor(adr: Address): AbstractCount = adr match {  //TODO: parameterise this instead of hacking it in...
    case _: VarAddr[_] | _: PtrAddr[_] => CountOne
    case _ => CountInf
  }
    // extend
  def extend(a: A, v: V): This = extendOption(a, v).getOrElse(this)
  def extendOption(a: A, v: V): Option[This] = content.get(a) match {
    case None if lattice.isBottom(v) => None
    case None => Some(LocalStore(content + (a -> ((v, lattice.refs(v), freshCountFor(a))))))
    case Some((oldValue, oldRefs, oldCount)) =>
      val newValue = lattice.join(oldValue, v)
      val newCount = oldCount.inc
      val subsumed = newValue == oldValue
      if (subsumed && newCount == oldCount) {
        None
      } else if (subsumed) {
        Some(LocalStore(content + (a -> ((oldValue, oldRefs, newCount)))))
      } else {
        // we assume that refs(X U Y) = refs(X) U refs(Y)
        val newRefs = oldRefs ++ lattice.refs(v)
        Some(LocalStore(content + (a -> ((newValue, newRefs, newCount)))))
      }
  }
  // update
  override def update(a: A, v: V): LocalStore[A,V] = content.get(a) match {
    case None => throw new Exception("Should not update unused address")
    case Some((_, _, CountOne)) => LocalStore(content + (a -> ((v, lattice.refs(v), CountOne))))
    case _ => extend(a, v)
  }
  // stop-and-copy style GC
  def collect(roots: Set[A]): This =
    scan(roots, Set.empty, Map.empty)
  @tailrec
  private def scan(toMove: Set[A], moved: Set[A], current: Map[A, (V, Set[A], AbstractCount)]): This =
    if (toMove.isEmpty) {
      LocalStore(current)
    } else {
      val addr = toMove.head
      val rest = toMove.tail
      if (moved(addr)) {
        scan(rest, moved, current)
      } else {
        val (updated, newRefs) = move(addr, current)
        scan(rest ++ newRefs, moved + addr, updated)
      }
    }
  private def move(addr: A, to: Map[A, (V, Set[A], AbstractCount)]): (Map[A, (V, Set[A], AbstractCount)], Set[A]) = content.get(addr) match {
    case None => (to, Set.empty) 
    case Some(s@(_, refs, _)) => (to + (addr -> s), refs)
  }
  // join
  def empty = LocalStore(Map.empty)
  def join(other: LocalStore[A,V]): LocalStore[A,V] = 
    LocalStore(other.content.foldLeft(content) { case (acc, (adr, (value, refs, count))) =>
      acc.get(adr) match {
        case None => acc + (adr -> ((value, refs, count)))
        case Some((accValue, accRefs, accCount)) => 
          acc + (adr -> ((lattice.join(accValue, value),
                          accRefs ++ refs,
                          accCount.join(count))))
        }
      }
    )
}

object LocalStore {
  def empty[A <: Address, V](implicit lattice: LatticeWithAddrs[V, A]): LocalStore[A,V] = LocalStore(Map.empty)
  def from[A <: Address, V](content: Iterable[(A, V)])(implicit lattice: LatticeWithAddrs[V, A]): LocalStore[A,V] = 
    content.foldLeft(empty)((acc, bnd) => acc.extend(bnd._1, bnd._2))
}

//
// STORE INSTANTIATIONS
//