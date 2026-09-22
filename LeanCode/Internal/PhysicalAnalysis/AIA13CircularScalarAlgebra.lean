import AIA11LiteralDecodedCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCircularForm
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularCurrentEnergy Grad.AnnularVariational
open Grad.AnnularTiltedReference Grad.AnnularGrades Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.ActualReferenceAssembly

theorem highMode_nonzero (mode : HighAnnularMode) : mode.val.1 ≠ 0 := by
  intro zero
  have bound := mode.property
  simp only [zero, abs_zero] at bound
  norm_num at bound

theorem highMultiplier_angular_identity (mode : HighAnnularMode) :
    (highMultiplier mode.val.1 : ℂ) * (mode.val.1 : ℂ) ^ 2 + 4 = (mode.val.1 : ℂ) ^ 2 := by
  have nz : (mode.val.1 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (highMode_nonzero mode)
  have actual : highMultiplier mode.val.1 * (mode.val.1 : ℝ) ^ 2 + 4 = (mode.val.1 : ℝ) ^ 2 := by
    rw [highMultiplier_high _ (highMode_not_low _ mode.property)]
    field_simp
    ring
  exact_mod_cast actual

/-- Exact scalar cancellation of the retained inverse and the angular primitive. -/
theorem circular_scalar_pairing {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (mode : HighAnnularMode) (dt rt ct s af cf : E) :
    -(inner ℂ ((Real.sqrt (highMultiplier mode.val.1) : ℂ) • dt)
        (-retainedBInverseMultiplier mode.val • ((Real.sqrt (highMultiplier mode.val.1) : ℂ) • s)) +
      inner ℂ ((Real.sqrt (highMultiplier mode.val.1) : ℂ) • ct)
        (-((Real.sqrt (highMultiplier mode.val.1) : ℂ) • cf)) +
      inner ℂ ((Real.sqrt (highMultiplier mode.val.1) : ℂ) • ((Complex.I * (mode.val.1 : ℂ)) • rt))
        (-((Real.sqrt (highMultiplier mode.val.1) : ℂ) • af) -
          (2 : ℂ) • (angularInverseMultiplier mode.val •
            (-retainedBInverseMultiplier mode.val • ((Real.sqrt (highMultiplier mode.val.1) : ℂ) • s))))) =
      inner ℂ dt s + 2 * inner ℂ rt s + (highMultiplier mode.val.1 : ℂ) *
        (inner ℂ ct cf + inner ℂ ((Complex.I * (mode.val.1 : ℂ)) • rt) af) := by
  have bnz : (highMultiplier mode.val.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (highMultiplier_positive mode).ne'
  have mnz : (mode.val.1 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (highMode_nonzero mode)
  have square : (Real.sqrt (highMultiplier mode.val.1) : ℂ) ^ 2 = (highMultiplier mode.val.1 : ℂ) := by
    exact_mod_cast Real.sq_sqrt (highMultiplier_positive mode).le
  simp only [retainedBInverseMultiplier, retainedBMultiplier, angularInverseMultiplier,
    if_neg (highMode_nonzero mode), inner_sub_right, inner_neg_right, inner_smul_left,
    inner_smul_right, map_mul, Complex.conj_ofReal, map_intCast, Complex.conj_I]
  field_simp
  ring_nf
  simp only [square]
  ring

end Grad.AnnularCircularForm
