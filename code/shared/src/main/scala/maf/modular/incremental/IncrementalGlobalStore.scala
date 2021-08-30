package maf.modular.incremental

import maf.core.Expression
import maf.language.change.CodeVersion._
import maf.modular._
import maf.modular.incremental.scheme.lattice.IncrementalAbstractDomain
import maf.util.benchmarks.Timeout
import maf.util.graph.Tarjan

/**
 * This trait improves upon a basic incremental analysis (with dependency and component invalidation) by introducing store "provenance" tracking and
 * store lowering.
 * @tparam Expr
 *   The type of the expressions under analysis.
 */
trait IncrementalGlobalStore[Expr <: Expression] extends IncrementalModAnalysis[Expr] with GlobalStore[Expr] with IncrementalAbstractDomain[Expr] {
  inter =>

  type SCA = Set[Addr]

  /* ****************************************** */
  /* ***** Provenance tracking for values ***** */
  /* ****************************************** */

  /** Keeps track of the provenance of values. For every address, couples every component with the value it has written to the address. */
  var provenance: Map[Addr, Map[Component, Value]] = Map().withDefaultValue(Map().withDefaultValue(lattice.bottom))

  /** Caches the addresses written by every component. Used to find addresses that are no longer written by a component. */
  var cachedWrites: Map[Component, Set[Addr]] = Map().withDefaultValue(Set())

  /** Computes the value that should reside at a given address according to the provenance information. */
  def provenanceValue(addr: Addr): Value = provenance(addr).values.fold(lattice.bottom)(lattice.join(_, _))

  /** Updates the provenance information for a specific component and address. */
  def updateProvenance(cmp: Component, addr: Addr, value: Value): Unit =
    provenance = provenance + (addr -> (provenance(addr) + (cmp -> value)))

  /* ******************************************** */
  /* ***** Managing cyclic value provenance ***** */
  /* ******************************************** */

  /**
   * For every component, stores a map of W ~> Set[R], where the values R are the "constituents" of W.
   * @note
   *   The data is separated by components, so it can be reset upon the reanalysis of a component.
   * @note
   *   We could also store it as R ~> Set[W], but the current approach seems slightly easier (doesn't require a foreach over the set `reads`).
   */
  var addressDependencies: Map[Component, Map[Addr, Set[Addr]]] = Map().withDefaultValue(Map().withDefaultValue(Set()))

  /**
   * Keeps track of all inferred SCCs of addresses during an incremental update. To avoid confusion with analysis components, we call these Strongly
   * Connected Addresses (SCC containing addresses).
   */
  var SCAs: Set[SCA] = Set()

  def computeSCAs(): Set[SCA] =
    Tarjan.scc[Addr](store.keySet, addressDependencies.values.flatten.groupBy(_._1).map({ case (w, wr) => (w, wr.flatMap(_._2).toSet) }))

  /** Keeps track of all "incoming" values to an SCA. */
  // TODO (maybe): merge with SCAs.
  var incomingValues: Map[SCA, Value] = Map().withDefaultValue(lattice.bottom)

  /**
   * Computes the join of all values "incoming" in this SCA. The join suffices, as the addresses in the SCA are inter-dependent (i.e., the analysis
   * will join everything together anyway).
   * @note
   *   This implementation computes the incoming value on a "per component" base, by using the provenance.
   * @note
   *   We do not distinguish between contributions by components that are partially incoming: if a component writes 2 values to an address and one is
   *   incoming, no incoming values will be detected. TODO Improve upon this?
   * @return
   *   The join of all values "incoming" in this SCA.
   */
  def incomingSCAValue(sca: SCA): Value = {
    /*
    cachedWrites.foldLeft(lattice.bottom) { case (value, (component, addresses)) =>
      addresses.intersect(sca).foldLeft(value) { case (value, addr) =>
        if (addressDependencies(component)(addr).union(sca).isEmpty)
          lattice.join(value, provenance(addr)(component))
        else value
      }
    }
     */
    var value = lattice.bottom
    cachedWrites.foreach { case (component, addresses) =>
      // All addresses of the SCA written by `component`...
      addresses.intersect(sca).foreach { addr =>
        // ...that were not influenced by an address in the SCA...
        if (addressDependencies(component)(addr).union(sca).isEmpty) {
          // ...contribute to the incoming value.
          value = lattice.join(value, provenance(addr)(component))
        }
      }
    }
    value
  }

  /* ****************************** */
  /* ***** Write invalidation ***** */
  /* ****************************** */

  /**
   * To be called when a write dependency is deleted. Possibly updates the store with a new value for the given address. An address that is no longer
   * written will be deleted.
   * @param cmp
   *   The component from which the write dependency is deleted.
   * @param addr
   *   The address corresponding to the deleted write dependency.
   */
  def deleteProvenance(cmp: Component, addr: Addr): Unit = {
    // Delete the provenance information corresponding to this component.
    provenance = provenance + (addr -> (provenance(addr) - cmp))
    // Compute the new value for the address and update it in the store.
    val value: Value = provenanceValue(addr)
    if (configuration.checkAsserts) assert(lattice.subsumes(inter.store(addr), value)) // The new value can never be greater than the old value.
    if (value != inter.store(addr)) {
      trigger(AddrDependency(addr)) // Trigger first, as the dependencies may be removed should the address be deleted.
      // Small memory optimisation: clean up addresses entirely when they become not written anymore. This will also cause return addresses to be removed upon component deletion.
      if (provenance(addr).isEmpty)
        deleteAddress(addr)
      else inter.store = inter.store + (addr -> value)
    }
  }

  /**
   * Deletes an address from the store. To be used when they are no longer written by any component.
   * @note
   *   Also removes possible dependencies on this address, as well as the address's provenance!
   */
  def deleteAddress(addr: Addr): Unit = {
    store -= addr // Delete the address in the actual store.
    provenance -= addr // Remove provenance information corresponding to the address (to ensure the right dependencies are triggered should the address be recreated and obtain the same value).
    deps -= AddrDependency(addr) // Given that the address is no longer in existence, dependencies on this address can be removed.
  }

  /* ********************************** */
  /* ***** Component invalidation ***** */
  /* ********************************** */

  /**
   * Called when a component is deleted. Removes the provenance information corresponding to the addresses written by the given component, thereby
   * possibly refining the analysis store.
   * @note
   *   As a small memory optimisation, also clears `addressDependencies`. This set would be cleared anyway upon recreation and reanalysis of the
   *   deleted component `cmp`.
   * @param cmp
   *   The component that is deleted.
   */
  override def deleteComponent(cmp: Component): Unit = {
    if (configuration.writeInvalidation) {
      cachedWrites(cmp).foreach(deleteProvenance(cmp, _))
      cachedWrites = cachedWrites - cmp
    }
    if (configuration.cyclicValueInvalidation)
      addressDependencies = addressDependencies - cmp
    super.deleteComponent(cmp)
  }

  /* *************************************************** */
  /* ***** Incremental value update and refinement ***** */
  /* *************************************************** */

  /**
   * To be called upon a commit, with the join of the values written by the component to the given address. Possibly updates the store and provenance
   * information, and triggers dependencies if the store is updated.
   * @param cmp
   *   The component that is committed.
   * @param addr
   *   The address in the store of value nw.
   * @param nw
   *   The join of all values written by cmp to the store at addr.
   * @return
   *   Returns a boolean indicating whether the address was updated, indicating whether the corresponding dependency should be triggered.
   */
  def updateAddrInc(cmp: Component, addr: Addr, nw: Value): Boolean = {
    val old = provenance(addr)(cmp)
    if (old == nw) return false // Nothing changed.
    // Else, there is some change. Note that both `old ⊏ nw` and `nw ⊏ old` - or neither - are possible.
    updateProvenance(cmp, addr, nw)
    val oldJoin = inter.store.getOrElse(addr, lattice.bottom) // The value currently at the given address.
    // If `old ⊑ nw` we can just use join, which is probably more efficient.
    val newJoin = if (lattice.subsumes(nw, old)) lattice.join(oldJoin, nw) else provenanceValue(addr)
    if (configuration.checkAsserts)
      assert(newJoin == provenanceValue(addr), s"$addr\n${lattice.compare(newJoin, provenanceValue(addr), "New join", "Provenance value")}")
    if (oldJoin == newJoin) return false // Even with this component writing a different value to addr, the store does not change.
    inter.store = inter.store + (addr -> newJoin)
    true
  }

  /* ************************************************************************* */
  /* ***** Incremental update: actually perform the incremental analysis ***** */
  /* ************************************************************************* */

  override def updateAnalysis(timeout: Timeout.T): Unit = {
    // If cycle invalidation is enabled, compute which addresses are interdependent.
    // TODO: how about changes to the SCCs during the reanalysis? New addresses can become part of a SCC or SCCs can become merged (or split)
    if (configuration.cyclicValueInvalidation) {
      SCAs = computeSCAs()
      //incomingValues = incomingValues + SCAs.map(s => (s, incomingSCAValue(s)))
      val addrs = SCAs.flatten
      addrs.flatMap(provenance).map(_._1).foreach(addToWorkList)
      addrs.foreach { addr =>
        store = store + (addr -> lattice.bottom)
        provenance -= addr
      }
      cachedWrites = cachedWrites.map({ case (k, v) => (k, v -- addrs) }).withDefaultValue(Set())
    }
    super.updateAnalysis(timeout)
    // Clear the data as it is no longer needed. (This is not really required but reduces the memory footprint of the result.)
    if (configuration.cyclicValueInvalidation) SCAs = Set()
  }

  /* ************************************ */
  /* ***** Intra-component analysis ***** */
  /* ************************************ */

  trait IncrementalGlobalStoreIntraAnalysis extends IncrementalIntraAnalysis with GlobalStoreIntra {
    intra =>

    /**
     * Keep track of the values written by a component to an address. For every address, stores the join of all values written during this
     * intra-component address.
     */
    // TODO: Perhaps collapse this data structure in the global provenance information (requires updating the information without triggers etc, but with joining).
    var intraProvenance: Map[Addr, Value] = Map().withDefaultValue(lattice.bottom)

    /* ------------------------------------ */
    /* ----- Intra-component analysis ----- */
    /* ------------------------------------ */

    /** Called upon the (re-)analysis of a component. Here, used to clear out data structures of the incremental global store. */
    abstract override def analyzeWithTimeout(timeout: Timeout.T): Unit = {
      if (configuration.cyclicValueInvalidation)
        addressDependencies = addressDependencies - component // Avoid data becoming wrong/outdated after an incremental update.
      super.analyzeWithTimeout(timeout)
    }

    /* ---------------------------------- */
    /* ----- Basic store operations ----- */
    /* ---------------------------------- */

    override def readAddr(addr: Addr): Value = {
      val value = super.readAddr(addr)
      if (configuration.cyclicValueInvalidation) lattice.addAddress(value, addr)
      else value
    }

    override def writeAddr(addr: Addr, v: Value): Boolean = {
      var value = v
      // Update the value flow information and reset the reads information.
      if (configuration.cyclicValueInvalidation) {
        // Get the annotations and remove them so they are not written to the store.
        val dependentAddresses = getAddresses(value)
        value = removeAddresses(value)
        // Store the dependencies.
        val newDependencies = addressDependencies(component)(addr) ++ dependentAddresses
        addressDependencies = addressDependencies + (component -> (addressDependencies(component) + (addr -> newDependencies)))
      }
      // Update the intra-provenance: for every address, keep the join of the values written to the address. Do this only after possible removal of annotations.
      intraProvenance = intraProvenance + (addr -> lattice.join(intraProvenance(addr), value))
      // Ensure the intra-store is updated so it can be used. TODO should updateAddrInc be used here (but working on the intra-store) for an improved precision?
      super.writeAddr(addr, value)
    }

    /* ------------------------------ */
    /* ----- Write invalidation ----- */
    /* ------------------------------ */

    /**
     * Registers the provenance information to the global provenance registry. Uses `updateAddrInc` to allow store refinements forthcoming from a
     * refinement of the provenance value, that were not registered due to the monotonicity of the store _during_ the intra-component analyses.
     *
     * @note
     *   Will also call updateAddrInc for addresses that were already updated by doWrite (but this is ok as the same value is used).
     */
    def registerProvenances(): Unit = intraProvenance.foreach({ case (addr, value) => updateAddrInc(component, addr, value) })

    /** Refines values in the store that are no longer written to by a component. */
    def refineWrites(): Unit = {
      // Writes performed during this intra-component analysis. Important: this only works when the entire component is reanalysed!
      val recentWrites = intraProvenance.keySet
      if (version == New) {
        // The addresses previously written to by this component, but that are no longer written by this component.
        val deltaW = cachedWrites(component) -- recentWrites
        deltaW.foreach(deleteProvenance(component, _))
      }
      cachedWrites = cachedWrites + (component -> recentWrites)
    }

    /* ------------------------------------- */
    /* ----- Cyclic write invalidation ----- */
    /* ------------------------------------- */

    /** Refines all values in this SCA to the value "incoming". */
    def refineSCA(sca: SCA, incoming: Value): Unit = {
      // Should be done for every address in the SCA because an SCC/SCA may contain "inner cycles".
      sca.foreach { addr =>
        inter.store += addr -> incoming
        intra.store += addr -> incoming
        provenance += (addr -> provenance(addr).map(kv => if (cachedReadDeps(kv._1).contains(AddrDependency(addr))) (kv._1, incoming) else kv))
        updateAddrInc(component, // Call updateAddrInc to ensure triggers happen.
                      addr,
                      incoming
        )
      }
    }

    /* ------------------ */
    /* ----- Commit ----- */
    /* ------------------ */

    /**
     * Called for every written address. Returns true if the dependency needs to be triggered.
     *
     * @note
     *   This function should be overridden to avoid the functionality of GlobalStore to be used. Otherwise this function could be merged into
     *   refineWrites.
     */
    override def doWrite(dep: Dependency): Boolean = dep match {
      case AddrDependency(addr) if configuration.writeInvalidation =>
        // There is no need to use the updateAddr function, as the store is updated by updateAddrInc.
        // Also, this would not work, as updateAddr only performs monotonic updates.
        updateAddrInc(component, addr, intraProvenance(addr))
      case _ => super.doWrite(dep)
    }

    /** First performs the commit. Then uses information inferred during the analysis of the component to refine the store if possible. */
    override def commit(): Unit = {
      // First do the super commit, which will cause the actual global store to be updated.
      // WI: Takes care of addresses that are written and caused a store update (see `doWrite`).
      super.commit()
      if (configuration.writeInvalidation) {
        // Refines the store by removing addresses that are no longer written or by using the provenance information to refine the values in the store.
        // WI: Takes care of addresses that are no longer written by this component.
        refineWrites()
        // Make sure all provenance values are correctly stored, even if no doWrite is triggered for the corresponding address.
        // WI: Takes care of addresses that are written and did not cause a store update.
        registerProvenances()
      }
      /*
      if (configuration.cyclicValueInvalidation && version == New) {
        // Compute the new SCAs and the corresponding incoming values.
        val newSCAs = computeSCAs().map(sca => (sca, incomingSCAValue(sca)))
        // Check which SCAs need to be cleaned and triggered.
        // * SCA remained equal but has lower incoming => refine.
        // * SCAs merged: incoming values are joined => Do nothing (this is automagic).
        // * New SCA: new incoming value needs to be computed => Do nothing (this is automagic as well).
        // * SCA split: new incoming values need to be computed => Check if the incoming values are lower than before and recompute if needed.
        // * SCA split and merged simultaneously: ?
        /*
        SCAs.foreach { sca =>
          val splits = newSCAs.filter(_._1.intersect(sca).nonEmpty)
          val oldIncoming = incomingValues(sca)
          if (splits.size == 1 && !lattice.subsumes(splits.head._2, oldIncoming)) { // The old SCA corresponds to exactly one new SCA, and the incoming value is refined.
            refineSCA(splits.head._1, splits.head._2)
          } else if (splits.size > 1) { // The addresses of the old SCA are scattered across new SCAs.
            splits.foreach(s => if (!lattice.subsumes(s._2, oldIncoming)) refineSCA(s._1, s._2))
          }
        }
       */
        // If SCAs are merged, check whether the new incoming value still subsumes the join of the old incoming values. If not: refine.
        val merges = newSCAs.map(s => (s, SCAs.filter(_.intersect(s._1).nonEmpty))) //.filter(_._2.size > 1)
        val mergeIncomingOld = merges.map(s => (s._1, s._2.map(incomingValues).fold(lattice.bottom)(lattice.join(_, _))))
        mergeIncomingOld.foreach { case ((sca, incoming), incomingOld) =>
          if (!lattice.subsumes(incoming, incomingOld))
            refineSCA(sca, incoming)
        }
        // Store the new SCAs with their new incoming values.
        incomingValues = incomingValues ++ newSCAs
        SCAs = newSCAs.map(_._1)
      }
       */
    }
  }
}
