import AJH8ClosedRadialKernelCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter
open scoped BigOperators ENNReal Topology ContDiff
namespace Grad.AnnularRadialSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularKernelContinuity

/-- Smoothness follows from actual matrix radial jets and their already
checked full moments. No smoothness of the reconstructed solution is assumed. -/
theorem smoothPolynomialFamily_matrixJets {source target : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (kernels : ℕ → (radius : RadialPoint) → RadialKernel parameters radius source target)
    (coefficients : ℕ → ℝ → (ℤ × ℤ) → (ComplexEuclidean source →L[ℂ] ComplexEuclidean target))
    (same : ∀ order radius shift input, (kernels order radius).entry shift input = coefficients order radius.val shift)
    (derivative : ∀ order shift radius, HasDerivAt (fun point => coefficients order point shift)
      (coefficients (order + 1) radius shift) radius)
    (regular : ∀ order, RegularKernelFamily (kernels order)) (order : ℕ) :
    SmoothPolynomialFamily parameters lower positive bounded.le (kernels order) := by
  intro power
  have bounds : ∀ order, ∃ constant : ℝ, 0 ≤ constant ∧ ∀ radius ∈ Icc lower 1, ∀ shift,
      ‖coefficients order radius shift‖ ≤ constant * (annularFrequency shift.1 shift.2 ^ (power + 4))⁻¹ := by
    intro order
    obtain ⟨constant, nonnegative, bound⟩ := (regular order).2 (power + 4)
    refine ⟨constant, nonnegative, ?_⟩
    intro radius inside shift
    let actual : RadialPoint := ⟨radius, (positive.le.trans inside.1), inside.2⟩
    have entry : (kernels order actual).entry shift (0,0) = coefficients order radius shift := same order actual shift (0,0)
    rw [← entry]
    exact ((kernels order actual).entry_le shift (0,0)).trans
      (fullKernelEntryNorm_decay _ (kernels order actual) (power + 4) constant (bound actual) shift)
  have smooth := matrixSeries_smooth parameters power lower 1 bounded coefficients derivative bounds order
  apply smooth.congr
  intro radius inside
  change polynomialKernelAction _ power (kernels order (collarRadius lower positive bounded.le radius)) = _
  rw [polynomialKernelAction_matrixSeries parameters _ power _
    (coefficients order (collarRadius lower positive bounded.le radius).val)
    (same order (collarRadius lower positive bounded.le radius))]
  rw [collarRadius_literal lower positive bounded.le radius inside]

/-- Finite matrix assembly preserves the actual radial derivative. -/
theorem rowMultiplicationEntry_hasDerivAt (dimension : ℕ)
    (coefficient next : Fin dimension → ℝ → (ℤ × ℤ) → ℂ)
    (derivative : ∀ component radius shift, HasDerivAt (fun point => coefficient component point shift)
      (next component radius shift) radius) (radius : ℝ) (shift input : ℤ × ℤ) :
    HasDerivAt (fun point => rowMultiplicationEntry dimension (fun component => coefficient component point) shift input)
      (rowMultiplicationEntry dimension (fun component => next component radius) shift input) radius := by
  unfold rowMultiplicationEntry
  exact (HasDerivAt.fun_sum (u := Finset.univ)
    (fun component _ => (derivative component radius shift).smul_const
      (Grad.GaugeCoefficients.Physical.Ledger.matrixUnit (input := dimension) (output := 1) 0 component)))

theorem matrixMultiplicationEntry_hasDerivAt (source target : ℕ)
    (coefficient next : Fin target → Fin source → ℝ → (ℤ × ℤ) → ℂ)
    (derivative : ∀ row column radius shift, HasDerivAt (fun point => coefficient row column point shift)
      (next row column radius shift) radius) (radius : ℝ) (shift input : ℤ × ℤ) :
    HasDerivAt (fun point => matrixMultiplicationEntry source target (fun row column => coefficient row column point) shift input)
      (matrixMultiplicationEntry source target (fun row column => next row column radius) shift input) radius := by
  unfold matrixMultiplicationEntry
  exact (HasDerivAt.fun_sum (u := Finset.univ)
    (fun row _ => HasDerivAt.fun_sum (u := Finset.univ)
      (fun column _ => (derivative row column radius shift).smul_const
        (Grad.GaugeCoefficients.Physical.Ledger.matrixUnit (input := source) (output := target) row column))))

end Grad.AnnularRadialSmoothness
