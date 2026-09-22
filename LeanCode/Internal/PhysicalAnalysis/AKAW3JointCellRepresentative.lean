import AKAW2CountableAngularEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.ActualNativeCellMoments
open Grad.GenericCarriers Grad.PDEBootstrap

variable {dimension : ℕ} {X : Type*} [MeasurableSpace X] (measure : Measure X)
    (field : ℤ → X → PhysicalValue dimension)

def jointCellRepresentative (point : X) : CellValues dimension :=
  ∑' cell : ℤ, cellSingle (PhysicalValue dimension) cell (field cell point)

omit [MeasurableSpace X] in
/-- The joint representative retains every cell whenever the actual pointwise
square sum is finite. -/
theorem jointCellRepresentative_same (point : X)
    (member : Memℓp (fun cell => field cell point) 2) (cell : ℤ) :
    jointCellRepresentative field point cell = field cell point := by
  let value : CellValues dimension := ⟨fun cell => field cell point,member⟩
  have sum := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) value
  have equal : jointCellRepresentative field point = value := sum.tsum_eq
  exact congrArg (fun value : CellValues dimension => value cell) equal

variable (measurable : ∀ cell, AEStronglyMeasurable (field cell) measure)

include measurable in
theorem jointCellRepresentative_aestronglyMeasurable :
    AEStronglyMeasurable (jointCellRepresentative field) measure :=
  AEStronglyMeasurable.tsum (fun cell =>
    (cellSingle (PhysicalValue dimension) cell).continuous.comp_aestronglyMeasurable (measurable cell))

include measurable in
theorem finiteCellEnergy_ae_memlp
    (finite : (∫⁻ point, ∑' cell : ℤ, ENNReal.ofReal (‖field cell point‖ ^ 2) ∂measure) < ⊤) :
    ∀ᵐ point ∂measure, Memℓp (fun cell => field cell point) 2 := by
  have density (cell : ℤ) : AEMeasurable (fun point => ENNReal.ofReal (‖field cell point‖ ^ 2)) measure :=
    ((measurable cell).norm.pow 2).aemeasurable.ennreal_ofReal
  have finitePoint := ae_lt_top' (AEMeasurable.tsum density) finite.ne
  filter_upwards [finitePoint] with point finitePoint
  apply (memℓp_gen_iff (p := 2) (by norm_num)).mpr
  have summable := ENNReal.summable_toReal finitePoint.ne
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _),ENNReal.toReal_ofNat,Real.rpow_two] using summable

include measurable in
theorem jointCellRepresentative_energy
    (finite : (∫⁻ point, ∑' cell : ℤ, ENNReal.ofReal (‖field cell point‖ ^ 2) ∂measure) < ⊤) :
    (∫⁻ point, ENNReal.ofReal (‖jointCellRepresentative field point‖ ^ 2) ∂measure) =
      ∫⁻ point, ∑' cell : ℤ, ENNReal.ofReal (‖field cell point‖ ^ 2) ∂measure := by
  apply lintegral_congr_ae
  filter_upwards [finiteCellEnergy_ae_memlp measure field measurable finite] with point member
  have square : ‖jointCellRepresentative field point‖ ^ 2 =
      ∑' cell : ℤ, ‖jointCellRepresentative field point cell‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using
      (lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (jointCellRepresentative field point))
  rw [square,ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _)
    (by simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (memℓp_gen_iff (p := 2) (by norm_num)).mp (jointCellRepresentative field point).property)]
  simp_rw [jointCellRepresentative_same field point member]

include measurable in
theorem jointCellRepresentative_memLp
    (finite : (∫⁻ point, ∑' cell : ℤ, ENNReal.ofReal (‖field cell point‖ ^ 2) ∂measure) < ⊤) :
    MemLp (jointCellRepresentative field) 2 measure := by
  have measurableJoint := jointCellRepresentative_aestronglyMeasurable measure field measurable
  apply (memLp_two_iff_integrable_sq_norm measurableJoint).mpr
  refine ⟨measurableJoint.norm.pow 2,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun _ => sq_nonneg _))).mpr
  rw [jointCellRepresentative_energy measure field measurable finite]
  exact finite

end Grad.ActualNativeCellMoments
