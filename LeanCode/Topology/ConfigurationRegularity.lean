import ReparametrizationBasic

noncomputable section

namespace Grad.MainAssembly.ConfigurationRegularity

open Grad.MainTarget

universe domainUniverse targetUniverse

/-- A local-extension witness can be reused at every lower differentiability
order without changing the extension or its agreement domain. -/
theorem hasLocalExtensions_of_order_le
    {Domain : Type domainUniverse} {Target : Type targetUniverse}
    [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (lower higher : Regularity) (orderBound : lower.order ≤ higher.order)
    (mapping : Domain → Target) (domain : Set Domain)
    (regularity : HasLocalExtensions higher mapping domain) :
    HasLocalExtensions lower mapping domain := by
  intro point pointInDomain
  rcases regularity point pointInDomain with
    ⟨neighborhood, neighborhoodOpen, pointInNeighborhood,
      extension, extensionSmooth, extensionAgreement⟩
  exact ⟨neighborhood, neighborhoodOpen, pointInNeighborhood,
    extension, extensionSmooth.of_le orderBound, extensionAgreement⟩

/-- Exact monotonicity of target regularity. -/
theorem hasRegularity_of_order_le
    {Target : Type targetUniverse}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (lower higher : Regularity) (orderBound : lower.order ≤ higher.order)
    (mapping : Reference → Target) (regularity : HasRegularity higher mapping) :
    HasRegularity lower mapping :=
  hasLocalExtensions_of_order_le lower higher orderBound
    (periodicLift mapping) cylinder regularity

/-- The embedding and differential-injectivity clauses are independent of the
regularity index, so only their local-extension witness must be weakened. -/
theorem isEmbeddingOfRegularity_of_order_le
    (lower higher : Regularity) (orderBound : lower.order ≤ higher.order)
    (mapping : Reference → Vec)
    (embedding : IsEmbeddingOfRegularity higher mapping) :
    IsEmbeddingOfRegularity lower mapping :=
  ⟨hasRegularity_of_order_le lower higher orderBound mapping embedding.1,
    embedding.2⟩

/-- Exact componentwise regularity weakening for target configurations. -/
theorem isConfiguration_of_order_le
    (lower higher : Regularity)
    (positionAndPressureOrder : lower.order ≤ higher.order)
    (magneticOrder : lower.predecessor.order ≤ higher.predecessor.order)
    (configuration : Representative)
    (validity : IsConfiguration higher configuration) :
    IsConfiguration lower configuration := by
  exact
    ⟨isEmbeddingOfRegularity_of_order_le lower higher
        positionAndPressureOrder configuration.position validity.1,
      hasRegularity_of_order_le lower.predecessor higher.predecessor
        magneticOrder configuration.magnetic validity.2.1,
      hasRegularity_of_order_le lower higher
        positionAndPressureOrder configuration.pressure validity.2.2⟩

theorem order_le_smooth (regularity : Regularity) :
    regularity.order ≤ Regularity.smooth.order := by
  cases regularity with
  | finite order =>
      simp only [Regularity.order]
      exact_mod_cast (show (order : ℕ∞) ≤ ⊤ from le_top)
  | smooth => exact le_rfl

theorem predecessorOrder_le_smooth (regularity : Regularity) :
    regularity.predecessor.order ≤ Regularity.smooth.predecessor.order := by
  cases regularity with
  | finite order =>
      simp only [Regularity.predecessor, Regularity.order]
      apply WithTop.coe_le_coe.mpr
      exact le_top
  | smooth => exact le_rfl

/-- A smooth target configuration is a configuration at every literal target
regularity, including the predecessor regularity required of its magnetic
component. -/
theorem isConfiguration_of_smooth
    (regularity : Regularity) (configuration : Representative)
    (validity : IsConfiguration .smooth configuration) :
    IsConfiguration regularity configuration :=
  isConfiguration_of_order_le regularity .smooth
    (order_le_smooth regularity) (predecessorOrder_le_smooth regularity)
    configuration validity

/-- The first conjunct of the exact physical conclusion supplies the validity
clause needed by `ModuliCurve` at any target regularity. -/
theorem isConfiguration_of_physicalConclusions
    (regularity : Regularity) (configuration : Representative)
    (cellLength : ℝ) (period : ℕ)
    (conclusions : PhysicalConclusions configuration cellLength period) :
    IsConfiguration regularity configuration :=
  isConfiguration_of_smooth regularity configuration conclusions.1

end Grad.MainAssembly.ConfigurationRegularity
