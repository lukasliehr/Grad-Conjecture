import AKU19AxisFiniteValueMaps

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped BigOperators
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds Grad.NonlinearProduct
open Grad.FlatSourceProjection Grad.GaugeCoefficients.Physical.Ledger

/-- A finite vector axis coefficient inserted into a fixed polynomial or
cutoff profile, as an actual original ACore linear map. -/
def vectorAxisProfileCore {parameters : PhaseParameters} {input output : ℕ}
    (profile : ComplexEuclidean input →ₗ[ℂ] ClosedJet output) :
    Grad.AxisCore.AxisSmoothCore parameters input →ₗ[ℂ] ACore parameters output :=
  ∑ component, (fixedAxisJetCore (profile (EuclideanSpace.single component 1))).comp
    (axisValueMap (componentValue input component))

theorem vectorAxisProfileCore_val {parameters : PhaseParameters} {input output : ℕ}
    (profile : ComplexEuclidean input →ₗ[ℂ] ClosedJet output)
    (data : Grad.AxisCore.AxisSmoothCore parameters input) (cell : ℤ) :
    (vectorAxisProfileCore profile data).val cell = profile (data.val cell) := by
  simp only [vectorAxisProfileCore, LinearMap.sum_apply, LinearMap.comp_apply,
    Submodule.coe_sum, Finset.sum_apply, fixedAxisJetCore_val, axisValueMap_val, componentValue_apply]
  change (∑ component, data.val cell component • profile (EuclideanSpace.single component 1)) = _
  simp only [← map_smul,← map_sum]
  apply congrArg profile
  apply PiLp.ext
  intro row
  simp [Pi.single_apply]

/-- Every fixed finite profile has a same-grade original-width bound.
The constant is quantified before the source axis data. -/
theorem vectorAxisProfileCore_bound {parameters : PhaseParameters} {input output : ℕ}
    (profile : ComplexEuclidean input →ₗ[ℂ] ClosedJet output) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ data : Grad.AxisCore.AxisSmoothCore parameters input,
      originalGradeNorm grade (vectorAxisProfileCore profile data) ≤
        constant * ‖Grad.AxisCore.axisEta parameters input grade data‖ := by
  choose constants nonnegative bounds using fun component : Fin input =>
    fixedAxisJetCore_bound (parameters := parameters) (profile (EuclideanSpace.single component 1)) grade
  refine ⟨∑ component, constants component * ‖componentValue input component‖,
    Finset.sum_nonneg (fun component _ => mul_nonneg (nonnegative component) (norm_nonneg _)),fun data => ?_⟩
  simp only [vectorAxisProfileCore, LinearMap.sum_apply, LinearMap.comp_apply]
  apply (originalGradeNorm_sum_le grade _ _).trans
  calc
    _ ≤ ∑ component, (constants component * ‖componentValue input component‖) *
        ‖Grad.AxisCore.axisEta parameters input grade data‖ := by
      apply Finset.sum_le_sum
      intro component _
      apply (bounds component (axisValueMap (componentValue input component) data)).trans
      apply (mul_le_mul_of_nonneg_left (axisValueMap_bound (componentValue input component) data grade)
        (nonnegative component)).trans_eq
      ring
    _ = _ := (Finset.sum_mul _ _ _).symm

end Grad.FinitePhysicalJetLift
