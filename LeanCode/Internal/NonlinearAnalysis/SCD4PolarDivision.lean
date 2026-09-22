import SCD3Hadamard

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial Grad.BoundaryTrace

def radialDirection (angle : ℝ) : SpatialPlane := collarPlane (0, angle)

def polarPlane (point : ℝ × ℝ) : SpatialPlane := collarPlane (1 - point.1, point.2)

theorem radialDirection_smooth : ContDiff ℝ ∞ radialDirection :=
  collarPlane_smooth.comp (contDiff_const.prodMk contDiff_id)

theorem polarPlane_smooth : ContDiff ℝ ∞ polarPlane :=
  collarPlane_smooth.comp ((contDiff_const.sub contDiff_fst).prodMk contDiff_snd)

theorem polarPlane_eq (radius angle : ℝ) :
    polarPlane (radius, angle) = radius • radialDirection angle := by
  ext coordinate
  fin_cases coordinate <;> simp [polarPlane, radialDirection, collarPlane]

theorem radialDirection_norm (angle : ℝ) : ‖radialDirection angle‖ = 1 := by
  rw [radialDirection, collarPlane_norm]
  norm_num

theorem polarPlane_norm (radius angle : ℝ) : ‖polarPlane (radius, angle)‖ = |radius| := by
  rw [polarPlane_eq, norm_smul, Real.norm_eq_abs, radialDirection_norm, mul_one]

def polarClosedPoint (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) : ClosedDisk :=
  ⟨polarPlane (radius, angle), by
    change ‖polarPlane (radius, angle)‖ ≤ 1
    rw [polarPlane_norm, abs_of_nonneg nonnegative]
    exact bounded⟩

/-- A smooth polar representative of the quotient of a flat field by r.
It is defined at r=0 and globally without singular division. -/
def dividedPolarValue {dimension : ℕ} (field : ClosedJet dimension)
    (point : ℝ × ℝ) : ComplexEuclidean dimension :=
  ∑ coordinate : Fin 2, (radialDirection point.2 coordinate) •
    rayAverageValue (shiftedClosedJet field (fun _ : Fin 1 => coordinate)) (polarPlane point)

theorem dividedPolarValue_smooth {dimension : ℕ} (field : ClosedJet dimension) :
    ContDiff ℝ ∞ (dividedPolarValue field) := by
  apply ContDiff.sum
  intro coordinate _
  exact (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) coordinate).contDiff.comp
    radialDirection_smooth).comp contDiff_snd).smul
    ((rayAverageValue_smooth _).comp polarPlane_smooth)

theorem dividedPolarValue_multiply {dimension : ℕ} (field : ClosedJet dimension)
    (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    radius • dividedPolarValue field (radius, angle) =
      field.value (polarClosedPoint radius angle nonnegative bounded) - field.value (ambientClosedDisk 0) := by
  rw [closedJet_hadamard, dividedPolarValue, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [smul_smul]
  congr 1
  change radius * radialDirection angle coordinate = polarPlane (radius, angle) coordinate
  rw [polarPlane_eq]
  rfl

theorem dividedPolarValue_flat {dimension : ℕ} (field : ClosedJet dimension)
    (flat : field.value (ambientClosedDisk 0) = 0)
    (radius angle : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1) :
    dividedPolarValue field (radius, angle) =
      radius⁻¹ • field.value (polarClosedPoint radius angle positive.le bounded) := by
  have equality := dividedPolarValue_multiply field radius angle positive.le bounded
  rw [flat, sub_zero] at equality
  rw [← equality, smul_smul, inv_mul_cancel₀ positive.ne', one_smul]

/-- The actual conjugated original quotient, on every annulus a<=r<=1.
The global polar representative is constructed, not assumed to have jets. -/
theorem weighted_dividedPolarValue {dimension : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (flat : field.value (ambientClosedDisk 0) = 0)
    (radius angle : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1) :
    dividedPolarValue (phaseWeightedJet parameters cell field) (radius, angle) =
      cartesianWeight parameters cell (polarPlane (radius, angle)) •
        (radius⁻¹ • field.value (polarClosedPoint radius angle positive.le bounded)) := by
  rw [dividedPolarValue_flat _ (by rw [phaseWeightedJet_value, flat, smul_zero])
    radius angle positive bounded, phaseWeightedJet_value]
  exact smul_comm _ _ _

theorem radialDirection_periodic : Function.Periodic radialDirection (2 * Real.pi) := by
  intro angle
  ext coordinate
  fin_cases coordinate <;> simp [radialDirection, collarPlane, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem polarPlane_periodic : Function.Periodic polarPlane (0, 2 * Real.pi) := by
  intro point
  rw [show point + (0, 2 * Real.pi) = (point.1, point.2 + 2 * Real.pi) by ext <;> simp,
    polarPlane_eq, radialDirection_periodic]
  exact (polarPlane_eq point.1 point.2).symm

theorem dividedPolarValue_periodic {dimension : ℕ} (field : ClosedJet dimension) :
    Function.Periodic (dividedPolarValue field) (0, 2 * Real.pi) := by
  intro point
  simp only [dividedPolarValue, Prod.snd_add]
  rw [polarPlane_periodic point, radialDirection_periodic point.2]

end Grad.SourceCollarDivision
