import AUB8ActualInverseLimit

noncomputable section
set_option maxHeartbeats 1200000
open Filter
open scoped Topology
namespace Grad.ActualUniformGlobal
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.OrdinaryDiskFaithfulness Grad.OrdinaryDiskCalculus
attribute [local instance] unitNormedSpace

/-- A faithful linear value map determines the linearity of a constructed lift. -/
def linearOfBulk {E F G : Type*} [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
    [Module ℂ E] [Module ℂ F] [Module ℂ G] (bulk : F →ₗ[ℂ] G) (faithful : Function.Injective bulk)
    (linear : E →ₗ[ℂ] G) (lift : E → F) (same : ∀ source, bulk (lift source) = linear source) : E →ₗ[ℂ] F where
  toFun := lift
  map_add' := by
    intro first second
    apply faithful
    rw [map_add, same, same, same, map_add]
  map_smul' := by
    intro scalar source
    apply faithful
    rw [map_smul, same, same, map_smul]
    rfl

def actualCompletedInverseLinear (grade : ℕ) (parameters : PhaseParameters) (parameter : ℝ) :
    unitDiskSobolev grade →ₗ[ℂ] unitDiskSobolev (grade + 2) :=
  linearOfBulk (unitDiskBulk (grade + 2)).toLinearMap (ordinaryBulk_injective parameters (grade + 2))
    ((fullWeakBulkOperator parameter).toLinearMap.comp (unitDiskBulk grade).toLinearMap)
    (actualCompletedInverseValue grade parameters parameter)
    (actualCompletedInverseValue_bulk grade parameters parameter)

/-- The actual bounded homogeneous high Robin inverse on every ordinary
Sobolev source grade, constructed as a strong angular-cutoff limit. -/
def actualCompletedInverse (grade : ℕ) (parameters : PhaseParameters) (parameter : ℝ) :
    unitDiskSobolev grade →L[ℂ] unitDiskSobolev (grade + 2) :=
  (actualCompletedInverseLinear grade parameters parameter).mkContinuous (finiteInverseConstant grade |parameter|)
    (actualCompletedInverseValue_bound grade |parameter| parameters parameter le_rfl)

theorem actualCompletedInverse_bulk (grade : ℕ) (parameters : PhaseParameters)
    (parameter : ℝ) (source : unitDiskSobolev grade) :
    unitDiskBulk (grade + 2) (actualCompletedInverse grade parameters parameter source) =
      fullWeakBulkOperator parameter (unitDiskBulk grade source) :=
  actualCompletedInverseValue_bulk grade parameters parameter source

theorem actualCompletedInverse_bound (grade : ℕ) (ceiling : ℝ) (parameters : PhaseParameters)
    (parameter : ℝ) (bounded : |parameter| ≤ ceiling) (source : unitDiskSobolev grade) :
    ‖actualCompletedInverse grade parameters parameter source‖ ≤ finiteInverseConstant grade ceiling * ‖source‖ :=
  actualCompletedInverseValue_bound grade ceiling parameters parameter bounded source

theorem actualCompletedInverse_tendsto (grade : ℕ) (parameters : PhaseParameters)
    (parameter : ℝ) (source : unitDiskSobolev grade) :
    Tendsto (fun modes : Finset ℤ => finiteCompletedInverse grade parameters parameter modes source) atTop
      (𝓝 (actualCompletedInverse grade parameters parameter source)) :=
  actualCompletedInverseValue_tendsto grade parameters parameter source

theorem actualCompletedInverse_highSource (grade : ℕ) (parameters : PhaseParameters)
    (parameter : ℝ) (source : unitDiskSobolev grade) (high : unitDiskBulk grade source ∈ highDiskL2) :
    unitDiskBulk (grade + 2) (actualCompletedInverse grade parameters parameter source) =
      highDiskBulk (highRobinWeakInverse parameter ⟨unitDiskBulk grade source, high⟩) := by
  have fixed : highL2ProjectionInto (unitDiskBulk grade source) = (⟨unitDiskBulk grade source, high⟩ : highDiskL2) :=
    Subtype.ext (highL2Projection_fixed ⟨unitDiskBulk grade source, high⟩)
  exact (actualCompletedInverse_bulk grade parameters parameter source).trans
    (congrArg (fun field : highDiskL2 => highDiskBulk (highRobinWeakInverse parameter field)) fixed)

/-- Actual full-source homogeneous gain. The solution represents the same
constructed weak inverse and therefore the full Cartesian weak PDE; every
constant precedes the original source and real parameter on its interval. -/
theorem actualHomogeneousTwoDerivativeGain (grade : ℕ) (ceiling : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (_parameters : PhaseParameters) (parameter : ℝ),
      |parameter| ≤ ceiling → ∀ (source : unitDiskSobolev grade) (high : unitDiskBulk grade source ∈ highDiskL2),
      ∃ solution : unitDiskSobolev (grade + 2),
        unitDiskBulk (grade + 2) solution = highDiskBulk (highRobinWeakInverse parameter ⟨unitDiskBulk grade source, high⟩) ∧
        HasDiskWeakLaplacian (unitDiskBulk (grade + 2) solution)
          (weakLaplacianValue parameter ⟨unitDiskBulk grade source, high⟩) ∧
        ‖solution‖ ≤ constant * ‖source‖ := by
  refine ⟨finiteInverseConstant grade ceiling, finiteInverseConstant_nonnegative grade ceiling, ?_⟩
  intro parameters parameter bounded source high
  refine ⟨actualCompletedInverse grade parameters parameter source,
    actualCompletedInverse_highSource grade parameters parameter source high, ?_,
    actualCompletedInverse_bound grade ceiling parameters parameter bounded source⟩
  rw [actualCompletedInverse_highSource grade parameters parameter source high]
  exact weakInverse_distribution parameter ⟨unitDiskBulk grade source, high⟩

end Grad.ActualUniformGlobal
