import ReparametrizationDerivative
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

noncomputable section

open Set
open scoped ContDiff Topology

namespace Grad.MainAssembly.TargetReparametrization

open Grad.MainTarget

local instance : Fact (0 < 2 * Real.pi) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

def packLinear : Plane × ℝ →ₗ[ℝ] Vec where
  toFun point := vector (point.1 0) (point.1 1) point.2
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;> rfl
  map_smul' scalar point := by
    ext coordinate
    fin_cases coordinate <;> rfl

theorem continuous_packLinear : Continuous packLinear :=
  packLinear.continuous_of_finiteDimensional

def referenceChartSection (chart : OpenPartialHomeomorph ℝ CellCircle)
    (point : Reference) : Vec :=
  packLinear (point.1.val, chart.symm point.2)

@[simp] theorem planarPart_referenceChartSection
    (chart : OpenPartialHomeomorph ℝ CellCircle) (point : Reference) :
    planarPart (referenceChartSection chart point) = point.1.val := by
  ext coordinate
  fin_cases coordinate <;> rfl

theorem referenceChartSection_mem_cylinder
    (chart : OpenPartialHomeomorph ℝ CellCircle) (point : Reference) :
    referenceChartSection chart point ∈ cylinder := by
  change ‖planarPart (referenceChartSection chart point)‖ ≤ 1
  rw [planarPart_referenceChartSection]
  exact point.1.property

theorem referenceChartSection_continuousAt
    (chart : OpenPartialHomeomorph ℝ CellCircle) (point : Reference)
    (angleInTarget : point.2 ∈ chart.target) :
    ContinuousAt (referenceChartSection chart) point := by
  apply continuous_packLinear.continuousAt.comp
  exact ((continuous_subtype_val.comp continuous_fst).continuousAt.prodMk
    (chart.continuousAt_symm angleInTarget |>.comp continuousAt_snd))

theorem quotientPoint_referenceChartSection
    (chart : OpenPartialHomeomorph ℝ CellCircle) (point : Reference)
    (angleInTarget : point.2 ∈ chart.target)
    (chartCoe : ∀ coordinate : ℝ, chart coordinate = (coordinate : CellCircle)) :
    quotientPoint (referenceChartSection chart point)
        (referenceChartSection_mem_cylinder chart point) = point := by
  apply Prod.ext
  · apply Subtype.ext
    exact planarPart_referenceChartSection chart point
  · change ((referenceChartSection chart point) 2 : CellCircle) = point.2
    have thirdCoordinate :
        (referenceChartSection chart point) 2 = chart.symm point.2 := by
      rfl
    rw [thirdCoordinate]
    rw [← chartCoe]
    exact chart.right_inv angleInTarget

/-- Any target map with actual regular local lifts is continuous on the
closed-disk times additive-circle reference body. -/
theorem continuous_of_hasRegularLocalLifts (regularity : Regularity)
    (mapping : Reference → Reference)
    (localLifts : HasRegularLocalLifts regularity mapping) : Continuous mapping := by
  rw [continuous_iff_continuousAt]
  intro referencePoint
  let representative : ℝ :=
    (AddCircle.equivIco (2 * Real.pi) 0 referencePoint.2).val
  have representativeCoe : (representative : CellCircle) = referencePoint.2 := by
    exact (AddCircle.equivIco (2 * Real.pi) 0).symm_apply_apply referencePoint.2
  let chartStart := representative - Real.pi
  let chart := AddCircle.openPartialHomeomorphCoe (2 * Real.pi) chartStart
  have chartCoe : ∀ coordinate : ℝ, chart coordinate = (coordinate : CellCircle) := by
    intro coordinate
    rfl
  have startIco : chartStart ∈
      Set.Ico chartStart (chartStart + 2 * Real.pi) :=
    ⟨le_rfl, lt_add_of_pos_right _ (mul_pos (by norm_num) Real.pi_pos)⟩
  have representativeIco : representative ∈
      Set.Ico chartStart (chartStart + 2 * Real.pi) := by
    constructor <;> dsimp only [chartStart] <;> linarith [Real.pi_pos]
  have angleInTarget : referencePoint.2 ∈ chart.target := by
    change referencePoint.2 ∈ {(chartStart : CellCircle)}ᶜ
    intro equality
    have coercedEquality : (representative : CellCircle) = (chartStart : CellCircle) :=
      representativeCoe.trans equality
    have realEquality :=
      (AddCircle.coe_eq_coe_iff_of_mem_Ico representativeIco startIco).mp coercedEquality
    dsimp only [chartStart] at realEquality
    linarith [Real.pi_pos]
  let localSection := referenceChartSection chart
  let ambientPoint := localSection referencePoint
  have ambientPointInCylinder : ambientPoint ∈ cylinder :=
    referenceChartSection_mem_cylinder chart referencePoint
  have sectionAtReference :
      quotientPoint ambientPoint ambientPointInCylinder = referencePoint := by
    exact quotientPoint_referenceChartSection chart referencePoint angleInTarget chartCoe
  have sectionContinuous : ContinuousAt localSection referencePoint :=
    referenceChartSection_continuousAt chart referencePoint angleInTarget
  rcases localLifts ambientPoint ambientPointInCylinder with
    ⟨liftNeighborhood, liftOpen, ambientPointInLift,
      localLift, liftSmooth, liftAgreement⟩
  have liftContinuous : ContinuousAt localLift ambientPoint :=
    (liftSmooth ambientPoint ambientPointInLift).contDiffAt
      (liftOpen.mem_nhds ambientPointInLift) |>.continuousAt
  have liftContinuousAtSection :
      ContinuousAt localLift (localSection referencePoint) := by
    simpa only [ambientPoint] using liftContinuous
  have eventuallyAngleTarget :
      ∀ᶠ point in nhds referencePoint, point.2 ∈ chart.target :=
    continuousAt_snd.preimage_mem_nhds (chart.open_target.mem_nhds angleInTarget)
  have eventuallySectionInLift :
      ∀ᶠ point in nhds referencePoint, localSection point ∈ liftNeighborhood :=
    sectionContinuous.preimage_mem_nhds (liftOpen.mem_nhds ambientPointInLift)
  have planarEventually :
      (fun point : Reference => planarPart (localLift (localSection point))) =ᶠ[nhds referencePoint]
        fun point => (mapping point).1.val := by
    filter_upwards [eventuallyAngleTarget, eventuallySectionInLift] with point
      pointAngleInTarget sectionInLift
    have sectionInCylinder := referenceChartSection_mem_cylinder chart point
    have sectionQuotient :=
      quotientPoint_referenceChartSection chart point pointAngleInTarget chartCoe
    obtain ⟨liftImageInCylinder, liftAtPoint⟩ :=
      liftAgreement (localSection point) sectionInLift sectionInCylinder
    have exactQuotient :
        quotientPoint (localLift (localSection point)) liftImageInCylinder = mapping point := by
      rw [liftAtPoint, sectionQuotient]
    exact congrArg (fun value : Reference => value.1.val) exactQuotient
  have circleEventually :
      (fun point : Reference => ((localLift (localSection point)) 2 : CellCircle))
        =ᶠ[nhds referencePoint] fun point => (mapping point).2 := by
    filter_upwards [eventuallyAngleTarget, eventuallySectionInLift] with point
      pointAngleInTarget sectionInLift
    have sectionInCylinder := referenceChartSection_mem_cylinder chart point
    have sectionQuotient :=
      quotientPoint_referenceChartSection chart point pointAngleInTarget chartCoe
    obtain ⟨liftImageInCylinder, liftAtPoint⟩ :=
      liftAgreement (localSection point) sectionInLift sectionInCylinder
    have exactQuotient :
        quotientPoint (localLift (localSection point)) liftImageInCylinder = mapping point := by
      rw [liftAtPoint, sectionQuotient]
    exact congrArg (fun value : Reference => value.2) exactQuotient
  have planarModelContinuous :
      ContinuousAt (fun point : Reference => planarPart (localLift (localSection point)))
        referencePoint :=
    Grad.MainTarget.SemanticBridges.continuous_planarPart.continuousAt.comp
      (liftContinuousAtSection.comp sectionContinuous)
  have planarOutputContinuous :
      ContinuousAt (fun point : Reference => (mapping point).1.val) referencePoint :=
    planarModelContinuous.congr planarEventually
  have diskOutputContinuous :
      ContinuousAt (fun point : Reference => (mapping point).1) referencePoint := by
    exact tendsto_subtype_rng.mpr planarOutputContinuous
  have angleModelContinuous :
      ContinuousAt (fun point : Reference => ((localLift (localSection point)) 2 : CellCircle))
        referencePoint :=
    (AddCircle.continuous_mk' (2 * Real.pi)).continuousAt.comp
      ((coordinateCLM 2).continuous.continuousAt.comp
        (liftContinuousAtSection.comp sectionContinuous))
  have angleOutputContinuous :
      ContinuousAt (fun point : Reference => (mapping point).2) referencePoint :=
    angleModelContinuous.congr circleEventually
  exact diskOutputContinuous.prodMk angleOutputContinuous

/-- Exact `NG_Z06_HOMEOMORPH`: a target reparametrization carries its given
reference equivalence to a homeomorphism, using its two stored local-lift
systems for the two continuity directions. -/
def reparametrizationHomeomorph (regularity : Regularity)
    (reparametrization : Reference ≃ Reference)
    (isReparametrization : IsReparametrization regularity reparametrization) :
    Reference ≃ₜ Reference where
  toEquiv := reparametrization
  continuous_toFun :=
    continuous_of_hasRegularLocalLifts regularity reparametrization isReparametrization.1
  continuous_invFun :=
    continuous_of_hasRegularLocalLifts regularity reparametrization.symm isReparametrization.2

end Grad.MainAssembly.TargetReparametrization
