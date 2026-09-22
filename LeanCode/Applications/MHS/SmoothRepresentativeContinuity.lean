import ConfigurationRegularity
import CylinderJets
import Mathlib.Topology.UniformSpace.Equicontinuity
import Mathlib.Analysis.Calculus.TangentCone.Prod

noncomputable section

open Set
open scoped ContDiff Pointwise Topology

namespace Grad.MainAssembly.SmoothRepresentativeContinuity

open Grad.MainTarget
open Grad.MainTarget.SemanticBridges

universe targetUniverse

def spatialInclusion : Vec →L[ℝ] ℝ × Vec :=
  ContinuousLinearMap.inr ℝ ℝ Vec

@[simp]
theorem spatialInclusion_apply (point : Vec) :
    spatialInclusion point = (0, point) := rfl

def shiftedParameterSet (parameter : ℝ) (parameterNeighborhood : Set ℝ) : Set ℝ :=
  {increment | parameter + increment ∈ parameterNeighborhood}

def shiftedProductDomain (parameter : ℝ)
    (parameterNeighborhood : Set ℝ) : Set (ℝ × Vec) :=
  shiftedParameterSet parameter parameterNeighborhood ×ˢ cylinder

theorem shiftedParameterSet_isOpen
    (parameter : ℝ) (parameterNeighborhood : Set ℝ)
    (parameterOpen : IsOpen parameterNeighborhood) :
    IsOpen (shiftedParameterSet parameter parameterNeighborhood) :=
  parameterOpen.preimage (continuous_const.add continuous_id)

theorem uniqueDiffOn_shiftedProductDomain
    (parameter : ℝ) (parameterNeighborhood : Set ℝ)
    (parameterOpen : IsOpen parameterNeighborhood) :
    UniqueDiffOn ℝ (shiftedProductDomain parameter parameterNeighborhood) :=
  (shiftedParameterSet_isOpen parameter parameterNeighborhood parameterOpen).uniqueDiffOn.prod
    uniqueDiffOn_cylinder

theorem spatialInclusion_preimage_shiftedProductDomain
    (parameter : ℝ) (parameterNeighborhood : Set ℝ)
    (parameterIn : parameter ∈ parameterNeighborhood) :
    spatialInclusion ⁻¹' shiftedProductDomain parameter parameterNeighborhood = cylinder := by
  ext point
  simp [shiftedProductDomain, shiftedParameterSet, parameterIn]

theorem translate_shiftedProductDomain
    (parameter : ℝ) (parameterNeighborhood : Set ℝ) :
    (parameter, (0 : Vec)) +ᵥ
      shiftedProductDomain parameter parameterNeighborhood =
        parameterNeighborhood ×ˢ cylinder := by
  ext point
  simp [mem_vadd_set_iff_neg_vadd_mem, shiftedProductDomain,
    shiftedParameterSet]

/-- At every point of the exact product domain, the spatial within jet of a
parameter slice is the joint within jet with every direction restricted to the
canonical spatial inclusion. -/
theorem slice_iteratedFDerivWithin_eq_joint
    {Target : Type targetUniverse}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (parameterNeighborhood : Set ℝ) (parameterOpen : IsOpen parameterNeighborhood)
    (mapping : ℝ × Vec → Target)
    (mappingSmooth : ContDiffOn ℝ ∞ mapping (parameterNeighborhood ×ˢ cylinder))
    (parameter : ℝ) (parameterIn : parameter ∈ parameterNeighborhood)
    (point : Vec) (pointIn : point ∈ cylinder) (order : ℕ) :
    iteratedFDerivWithin ℝ order (fun spatial => mapping (parameter, spatial))
        cylinder point =
      (iteratedFDerivWithin ℝ order mapping
        (parameterNeighborhood ×ˢ cylinder) (parameter, point)).compContinuousLinearMap
          (fun _ => spatialInclusion) := by
  let base : ℝ × Vec := (parameter, 0)
  have shiftedSmooth : ContDiffOn ℝ ∞ (fun argument => mapping (base + argument))
      (shiftedProductDomain parameter parameterNeighborhood) := by
    apply mappingSmooth.comp
      (contDiff_const.add contDiff_id).contDiffOn
    intro argument argumentIn
    constructor
    · simpa [base, shiftedProductDomain, shiftedParameterSet] using argumentIn.1
    · simpa [base] using argumentIn.2
  have preimageEquality := spatialInclusion_preimage_shiftedProductDomain
    parameter parameterNeighborhood parameterIn
  have translatedEquality := translate_shiftedProductDomain
    parameter parameterNeighborhood
  have compositionFormula := spatialInclusion.iteratedFDerivWithin_comp_right
    shiftedSmooth
    (uniqueDiffOn_shiftedProductDomain parameter parameterNeighborhood parameterOpen)
    (by rw [preimageEquality]; exact uniqueDiffOn_cylinder)
    (x := point)
    (by
      change point ∈ spatialInclusion ⁻¹'
        shiftedProductDomain parameter parameterNeighborhood
      rw [preimageEquality]
      exact pointIn)
    (i := order)
    (by exact_mod_cast (show (order : ℕ∞) ≤ ⊤ from le_top))
  rw [preimageEquality] at compositionFormula
  have shiftedDerivative := iteratedFDerivWithin_comp_add_left (𝕜 := ℝ)
    (f := mapping) (s := shiftedProductDomain parameter parameterNeighborhood)
    order base (spatialInclusion point)
  rw [translatedEquality] at shiftedDerivative
  have sliceAsComposition :
      (fun spatial => mapping (parameter, spatial)) =
        (fun argument => mapping (base + argument)) ∘ spatialInclusion := by
    funext spatial
    simp [base]
  rw [sliceAsComposition]
  calc
    _ = (iteratedFDerivWithin ℝ order (fun argument => mapping (base + argument))
          (shiftedProductDomain parameter parameterNeighborhood)
          (spatialInclusion point)).compContinuousLinearMap
            (fun _ => spatialInclusion) := compositionFormula
    _ = _ := by
      rw [shiftedDerivative]
      simp [base]

/-- The exact product domain stored by `SmoothRepresentatives` has unique
within derivatives whenever its parameter neighborhood is open. -/
theorem uniqueDiffOn_parameter_prod_cylinder
    (parameterNeighborhood : Set ℝ)
    (parameterOpen : IsOpen parameterNeighborhood) :
    UniqueDiffOn ℝ (parameterNeighborhood ×ˢ cylinder) :=
  parameterOpen.uniqueDiffOn.prod uniqueDiffOn_cylinder

def spatialRestriction {Target : Type targetUniverse}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target] (order : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin order => ℝ × Vec) Target →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin order => Vec) Target :=
  ContinuousMultilinearMap.compContinuousLinearMapL (F := Target)
    (fun _ => spatialInclusion)

@[simp]
theorem spatialRestriction_apply {Target : Type targetUniverse}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target] (order : ℕ)
    (jet : ContinuousMultilinearMap ℝ (fun _ : Fin order => ℝ × Vec) Target) :
    spatialRestriction order jet =
      jet.compContinuousLinearMap (fun _ => spatialInclusion) := rfl

theorem continuousOn_spatiallyRestricted_jointJet
    {Target : Type targetUniverse}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (parameterNeighborhood : Set ℝ) (parameterOpen : IsOpen parameterNeighborhood)
    (mapping : ℝ × Vec → Target)
    (mappingSmooth : ContDiffOn ℝ ∞ mapping (parameterNeighborhood ×ˢ cylinder))
    (order : ℕ) :
    ContinuousOn (fun argument =>
      spatialRestriction order
        (iteratedFDerivWithin ℝ order mapping
          (parameterNeighborhood ×ˢ cylinder) argument))
      (parameterNeighborhood ×ˢ cylinder) := by
  have derivativeContinuous : ContinuousOn
      (iteratedFDerivWithin ℝ order mapping
        (parameterNeighborhood ×ˢ cylinder))
      (parameterNeighborhood ×ˢ cylinder) :=
    mappingSmooth.continuousOn_iteratedFDerivWithin
      (show ((order : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) from
        WithTop.coe_le_coe.mpr le_top)
      (uniqueDiffOn_parameter_prod_cylinder parameterNeighborhood parameterOpen)
  exact (spatialRestriction (Target := Target) order).continuous.comp_continuousOn'
    derivativeContinuous

theorem isClosed_fundamentalCylinder : IsClosed fundamentalCylinder := by
  have closedCylinder : IsClosed cylinder :=
    isClosed_le continuous_planarPart.norm continuous_const
  have coordinateContinuous : Continuous (fun point : Vec => point 2) := by
    fun_prop
  have closedLower : IsClosed {point : Vec | 0 ≤ point 2} :=
    isClosed_le continuous_const coordinateContinuous
  have closedUpper : IsClosed {point : Vec | point 2 ≤ 2 * Real.pi} :=
    isClosed_le coordinateContinuous continuous_const
  have setEquality : fundamentalCylinder =
      (cylinder ∩ {point : Vec | 0 ≤ point 2}) ∩
        {point : Vec | point 2 ≤ 2 * Real.pi} := by
    ext point
    constructor
    · intro membership
      exact ⟨⟨membership.1, membership.2.1⟩, membership.2.2⟩
    · rintro ⟨⟨inCylinder, lowerBound⟩, upperBound⟩
      exact ⟨inCylinder, lowerBound, upperBound⟩
  rw [setEquality]
  exact (closedCylinder.inter closedLower).inter closedUpper

/-- The exact compact spatial set used by every target uniform jet really is
compact; this is the compactness input for parameter-uniform convergence. -/
theorem isCompact_fundamentalCylinder : IsCompact fundamentalCylinder := by
  let coordinateBox : Set Vec :=
    (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)) ⁻¹'
      Set.pi Set.univ (fun _ => Set.Icc (-(max 1 (2 * Real.pi))) (max 1 (2 * Real.pi)))
  have boxCompact : IsCompact coordinateBox := by
    exact (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).isCompact_preimage.mpr
      (isCompact_univ_pi fun _ => isCompact_Icc)
  apply IsCompact.of_isClosed_subset boxCompact isClosed_fundamentalCylinder
  intro point pointIn
  dsimp [coordinateBox]
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  intro index
  change -(max 1 (2 * Real.pi)) ≤ point index ∧
    point index ≤ max 1 (2 * Real.pi)
  fin_cases index
  · have coordinateBound : |point 0| ≤ 1 := by
      calc
        |point 0| = ‖planarPart point 0‖ := by simp [planarPart]
        _ ≤ ‖planarPart point‖ := PiLp.norm_apply_le _ _
        _ ≤ 1 := pointIn.1
    rcases abs_le.mp coordinateBound with ⟨lowerBound, upperBound⟩
    exact ⟨lowerBound.trans' (neg_le_neg (le_max_left 1 (2 * Real.pi))),
      upperBound.trans (le_max_left 1 (2 * Real.pi))⟩
  · have coordinateBound : |point 1| ≤ 1 := by
      calc
        |point 1| = ‖planarPart point 1‖ := by simp [planarPart]
        _ ≤ ‖planarPart point‖ := PiLp.norm_apply_le _ _
        _ ≤ 1 := pointIn.1
    rcases abs_le.mp coordinateBound with ⟨lowerBound, upperBound⟩
    exact ⟨lowerBound.trans' (neg_le_neg (le_max_left 1 (2 * Real.pi))),
      upperBound.trans (le_max_left 1 (2 * Real.pi))⟩
  · exact ⟨pointIn.2.1.trans' (by linarith [le_max_left 1 (2 * Real.pi)]),
      pointIn.2.2.trans (le_max_right 1 (2 * Real.pi))⟩

/-- Joint smoothness on a parameter neighborhood and the exact closed cylinder
implies continuity, in uniform convergence on the literal fundamental
cylinder, of every spatial within-jet of the parameter slices. -/
theorem continuous_spatialJets_of_jointSmooth
    {Target : Type targetUniverse}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (interval parameterNeighborhood : Set ℝ)
    [WeaklyLocallyCompactSpace interval]
    (intervalSubset : interval ⊆ parameterNeighborhood)
    (parameterOpen : IsOpen parameterNeighborhood)
    (mapping : ℝ × Vec → Target)
    (mappingSmooth : ContDiffOn ℝ ∞ mapping (parameterNeighborhood ×ˢ cylinder))
    (order : ℕ) :
    Continuous (fun parameter : interval =>
      UniformFun.ofFun (fun point : fundamentalCylinder =>
        iteratedFDerivWithin ℝ order
          (fun spatial => mapping (parameter, spatial)) cylinder point)) := by
  let _ : CompactSpace fundamentalCylinder :=
    isCompact_iff_compactSpace.mp isCompact_fundamentalCylinder
  let jointFamily : interval → fundamentalCylinder →
      ContinuousMultilinearMap ℝ (fun _ : Fin order => Vec) Target :=
    fun parameter point => spatialRestriction order
      (iteratedFDerivWithin ℝ order mapping
        (parameterNeighborhood ×ˢ cylinder) (parameter, point))
  have jointContinuousOn := continuousOn_spatiallyRestricted_jointJet
    parameterNeighborhood parameterOpen mapping mappingSmooth order
  have inclusionContinuous : Continuous
      (fun pair : interval × fundamentalCylinder =>
        ((pair.1.val, pair.2.val) : ℝ × Vec)) := by
    fun_prop
  have jointUncurryContinuous : Continuous ↿jointFamily := by
    have compositionContinuous := jointContinuousOn.comp_continuous
      inclusionContinuous (fun pair =>
        ⟨intervalSubset pair.1.property, pair.2.property.1⟩)
    change Continuous (fun pair : interval × fundamentalCylinder =>
      spatialRestriction order
        (iteratedFDerivWithin ℝ order mapping
          (parameterNeighborhood ×ˢ cylinder) (pair.1, pair.2)))
    exact compositionContinuous
  have jointUniformContinuous : Continuous (fun parameter : interval =>
      UniformFun.ofFun (jointFamily parameter)) := by
    rw [continuous_iff_continuousAt]
    intro parameter
    rw [ContinuousAt, UniformFun.tendsto_iff_tendstoUniformly]
    change TendstoUniformly jointFamily (jointFamily parameter) (𝓝 parameter)
    exact jointUncurryContinuous.tendstoUniformly jointFamily parameter
  have familyEquality :
      (fun parameter : interval =>
        UniformFun.ofFun (fun point : fundamentalCylinder =>
          iteratedFDerivWithin ℝ order
            (fun spatial => mapping (parameter, spatial)) cylinder point)) =
      (fun parameter : interval => UniformFun.ofFun (jointFamily parameter)) := by
    funext parameter
    apply congrArg UniformFun.ofFun
    funext point
    exact slice_iteratedFDerivWithin_eq_joint parameterNeighborhood parameterOpen
      mapping mappingSmooth parameter (intervalSubset parameter.property)
      point point.property.1 order
  rw [familyEquality]
  exact jointUniformContinuous

theorem continuous_componentJets_of_smoothExtension
    {Target : Type targetUniverse}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (interval parameterNeighborhood : Set ℝ)
    [WeaklyLocallyCompactSpace interval]
    (intervalSubset : interval ⊆ parameterNeighborhood)
    (parameterOpen : IsOpen parameterNeighborhood)
    (family : interval → Representative) (extension : ℝ → Representative)
    (extensionAgreement : ∀ parameter : interval,
      extension parameter = family parameter)
    (component : Representative → Reference → Target)
    (jointExtensions : HasLocalExtensions .smooth
      (fun argument : ℝ × Vec =>
        periodicLift (component (extension argument.1)) argument.2)
      (parameterNeighborhood ×ˢ cylinder))
    (regularity : Regularity) :
    Continuous (fun parameter : interval =>
      jets regularity (component (family parameter))) := by
  apply continuous_pi
  intro order
  have sliceContinuous := continuous_spatialJets_of_jointSmooth
    interval parameterNeighborhood intervalSubset parameterOpen
    (fun argument : ℝ × Vec =>
      periodicLift (component (extension argument.1)) argument.2)
    (localExtensions_contDiffOn jointExtensions) order.val
  change Continuous (fun parameter : interval =>
    UniformFun.ofFun (fun point : fundamentalCylinder =>
      iteratedFDerivWithin ℝ order.val
        (periodicLift (component (family parameter))) cylinder point))
  convert sliceContinuous using 1
  funext parameter
  apply congrArg UniformFun.ofFun
  funext point
  change iteratedFDerivWithin ℝ order.val
      (periodicLift (component (family parameter))) cylinder point =
    iteratedFDerivWithin ℝ order.val
      (periodicLift (component (extension parameter))) cylinder point
  rw [extensionAgreement parameter]

/-- The joint smooth representatives required by the frozen theorem statement
already imply continuity of the literal dependent configuration curve for its
induced all-jet topology. -/
theorem configurationCurve_continuous_of_smoothRepresentatives
    (interval : Set ℝ) [WeaklyLocallyCompactSpace interval]
    (family : interval → Representative)
    (smoothRepresentatives : SmoothRepresentatives interval family)
    (regularity : Regularity)
    (validity : ∀ parameter, IsConfiguration regularity (family parameter)) :
    Continuous (fun parameter =>
      (⟨family parameter, validity parameter⟩ : Configuration regularity)) := by
  rcases smoothRepresentatives with
    ⟨parameterNeighborhood, parameterOpen, intervalSubset, extension,
      extensionAgreement, positionExtensions, magneticExtensions, pressureExtensions⟩
  have positionContinuous : Continuous (fun parameter : interval =>
      jets regularity (family parameter).position) :=
    continuous_componentJets_of_smoothExtension interval parameterNeighborhood
      intervalSubset parameterOpen family extension extensionAgreement
      Representative.position positionExtensions regularity
  have magneticContinuous : Continuous (fun parameter : interval =>
      jets regularity.predecessor (family parameter).magnetic) :=
    continuous_componentJets_of_smoothExtension interval parameterNeighborhood
      intervalSubset parameterOpen family extension extensionAgreement
      Representative.magnetic magneticExtensions regularity.predecessor
  have pressureContinuous : Continuous (fun parameter : interval =>
      jets regularity (family parameter).pressure) :=
    continuous_componentJets_of_smoothExtension interval parameterNeighborhood
      intervalSubset parameterOpen family extension extensionAgreement
      Representative.pressure pressureExtensions regularity
  apply continuous_induced_rng.mpr
  change Continuous (fun parameter : interval =>
    (jets regularity (family parameter).position,
      jets regularity.predecessor (family parameter).magnetic,
      jets regularity (family parameter).pressure))
  fun_prop

end Grad.MainAssembly.SmoothRepresentativeContinuity
