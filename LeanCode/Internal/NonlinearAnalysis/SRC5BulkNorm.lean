import SRC4LiteralCore

noncomputable section

open scoped BigOperators

namespace Grad.SourceCollarBulk

open Grad.ClosedJets Grad.CartesianState Grad.AxisCore Grad.QuotientProjection
open Grad.FlatSourceProjection Grad.SourceCollarRestriction
open Grad.NonlinearProduct Grad.NonlinearQuotientBounds

/-- The common constant for the three planar completed BS36 graphs. -/
def planarBulkConstant (tangential : ℕ) : ℝ :=
  2 * (2 : ℝ) ^ (tangential + 1) *
    restrictionGraphConstant (tangential + 1) 1

/-- A single positive constant controlling all four completed bulk coordinates.
It keeps the exact `L⁻¹` dependence of the fourth source. -/
def sourceBulkConstant (L : ℝ) (tangential : ℕ) : ℝ :=
  1 + 3 * planarBulkConstant tangential +
    L⁻¹ * restrictionGraphConstant tangential 1

theorem planarBulkConstant_nonnegative (tangential : ℕ) :
    0 ≤ planarBulkConstant tangential := by
  unfold planarBulkConstant
  exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _))
    (restrictionGraphConstant_nonnegative (tangential + 1) 1)

theorem sourceBulkConstant_positive (L : ℝ) (LPositive : 0 < L)
    (tangential : ℕ) :
    0 < sourceBulkConstant L tangential := by
  unfold sourceBulkConstant
  have restrictionNonnegative := restrictionGraphConstant_nonnegative tangential 1
  have inverseNonnegative : 0 ≤ L⁻¹ := inv_nonneg.mpr LPositive.le
  nlinarith [planarBulkConstant_nonnegative tangential,
    mul_nonneg inverseNonnegative restrictionNonnegative]

/-- The diagonal angular map turns every literal `nu^(p+1)` restriction
row, including every weak radial derivative, into the exact
`im * nu^p` row. -/
theorem annularAngularRatio_restrictionModeLp {dimension : ℕ}
    (lower : ℝ) (power radial : ℕ) (parameters : PhaseParameters)
    (field : ACore parameters dimension) (mode : ℤ × ℤ) :
    annularAngularRatio mode •
        restrictionModeLp lower (power + 1) radial parameters field mode =
      (Complex.I * (mode.1 : ℂ)) •
        restrictionModeLp lower power radial parameters field mode := by
  unfold restrictionModeLp
  rw [smul_smul, smul_smul, annularAngularRatio_weight]

/-- Exact completed BS36 bulk estimate on the literal original fourfold
Hilbert source. The left side is the complete sum of the `F0`, genuine `RF0`,
`F1`, and `F2` weak radial graph norms; no point evaluation of completed data
occurs. -/
theorem completedSourceBulk_bound
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (L : ℝ) (LPositive : 0 < L)
    (tangential : ℕ) (source : ZAmbient parameters (tangential + 2)) :
    ‖completedForceTangential lower positive bounded parameters tangential source‖ +
        ‖completedForceAngular lower positive bounded parameters tangential source‖ +
        ‖completedForceRadial lower positive bounded parameters tangential source‖ +
        ‖completedFourthSource lower positive bounded parameters L tangential source‖ ≤
      sourceBulkConstant L tangential * ‖source‖ := by
  have force := completedForceTangential_bound lower positive bounded parameters tangential source
  have angular := completedForceAngular_bound lower positive bounded parameters tangential source
  have radial := completedForceRadial_bound lower positive bounded parameters tangential source
  have fourth := completedFourthSource_bound lower positive bounded parameters L LPositive tangential source
  have sourceNonnegative : 0 ≤ ‖source‖ := norm_nonneg _
  calc
    _ ≤ planarBulkConstant tangential * ‖source‖ +
          planarBulkConstant tangential * ‖source‖ +
          planarBulkConstant tangential * ‖source‖ +
          (L⁻¹ * restrictionGraphConstant tangential 1) * ‖source‖ :=
      add_le_add (add_le_add (add_le_add force angular) radial) fourth
    _ = (3 * planarBulkConstant tangential +
          L⁻¹ * restrictionGraphConstant tangential 1) * ‖source‖ := by ring
    _ ≤ sourceBulkConstant L tangential * ‖source‖ := by
      unfold sourceBulkConstant
      nlinarith

/-- On the dense smooth core, the completed input norm is exactly the
original BS3 fourfold source norm, including its factor two on the Cartesian
planar field. -/
theorem originalSource_completed_norm_sq (parameters : PhaseParameters)
    (tangential : ℕ) (source : SmoothQuotient parameters) :
    ‖quotientEta parameters (tangential + 2) source‖ ^ 2 =
      2 * (originalGradeNorm (tangential + 2) (cartesianSpinFirst source) ^ 2 +
        originalGradeNorm (tangential + 2) (cartesianSpinSecond source) ^ 2) +
        originalGradeNorm (tangential + 2) (source 2) ^ 2 +
        originalGradeNorm (tangential + 2) (source 3) ^ 2 := by
  change quotientNorm parameters (tangential + 2) source ^ 2 = _
  exact originalSpin_cartesian_components_norm parameters (tangential + 2) source

end Grad.SourceCollarBulk
