import AIX1ActualDisplacementCharacters

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularKernelOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction

variable {src tgt : ℕ} {parameters : PhaseParameters}

/-- Polynomial displacement multipliers act on the full input-dependent
kernel; the actual supremum envelope is retained by the accepted constructor. -/
def displacementKernel (kernel : FullTwoFrequencyKernel parameters src tgt)
    (scalar : (ℤ × ℤ) → ℂ) (degree : ℕ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (scalarBound : ∀ shift, ‖scalar shift‖ ≤ constant * annularFrequency shift.1 shift.2 ^ degree) :
    FullTwoFrequencyKernel parameters src tgt :=
  fullKernelOfEntries parameters (fun shift input => scalar shift • kernel.entry shift input)
    (fun shift => constant * annularFrequency shift.1 shift.2 ^ degree * kernel.entryNorm shift)
    (by
      intro shift input
      rw [norm_smul]
      exact mul_le_mul (scalarBound shift) (kernel.entry_le shift input) (norm_nonneg _)
        (mul_nonneg nonnegative (pow_nonneg (annularFrequency_pos shift).le _)))
    (by
      intro moment
      apply ((kernel.moments (moment + degree)).mul_left constant).congr
      intro shift
      rw [pow_add]
      ring)

@[simp] theorem displacementKernel_entry (kernel : FullTwoFrequencyKernel parameters src tgt)
    (scalar : (ℤ × ℤ) → ℂ) (degree : ℕ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (scalarBound : ∀ shift, ‖scalar shift‖ ≤ constant * annularFrequency shift.1 shift.2 ^ degree)
    (shift input : ℤ × ℤ) :
    (displacementKernel kernel scalar degree constant nonnegative scalarBound).entry shift input =
      scalar shift • kernel.entry shift input := rfl

theorem displacementKernel_entryNorm_le (kernel : FullTwoFrequencyKernel parameters src tgt)
    (scalar : (ℤ × ℤ) → ℂ) (degree : ℕ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (scalarBound : ∀ shift, ‖scalar shift‖ ≤ constant * annularFrequency shift.1 shift.2 ^ degree)
    (shift : ℤ × ℤ) :
    (displacementKernel kernel scalar degree constant nonnegative scalarBound).entryNorm shift ≤
      constant * annularFrequency shift.1 shift.2 ^ degree * kernel.entryNorm shift :=
  fullKernelOfEntries_entryNorm_le _ _ _ _ _ _

theorem displacementKernel_moment_le (kernel : FullTwoFrequencyKernel parameters src tgt)
    (scalar : (ℤ × ℤ) → ℂ) (degree : ℕ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (scalarBound : ∀ shift, ‖scalar shift‖ ≤ constant * annularFrequency shift.1 shift.2 ^ degree)
    (moment : ℕ) :
    fullKernelMoment parameters moment (displacementKernel kernel scalar degree constant nonnegative scalarBound) ≤
      constant * fullKernelMoment parameters (moment + degree) kernel := by
  have point (shift : ℤ × ℤ) := mul_le_mul_of_nonneg_left
    (displacementKernel_entryNorm_le kernel scalar degree constant nonnegative scalarBound shift)
    (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters shift)
      (pow_nonneg (annularFrequency_pos shift).le moment))
  calc
    _ ≤ ∑' shift : ℤ × ℤ, constant *
        (boundaryCoefficientPhaseCost parameters shift * annularFrequency shift.1 shift.2 ^ (moment + degree) * kernel.entryNorm shift) := by
      apply ((displacementKernel kernel scalar degree constant nonnegative scalarBound).moments moment).tsum_le_tsum _
        ((kernel.moments (moment + degree)).mul_left constant)
      intro shift
      convert point shift using 1
      rw [pow_add]
      ring
    _ = _ := by rw [tsum_mul_left]; rfl

/-- Exact two-angular/cell translation orbit with the original shift sign. -/
def kernelOrbit (tau : OrbitParameter) (kernel : FullTwoFrequencyKernel parameters src tgt) :
    FullTwoFrequencyKernel parameters src tgt :=
  displacementKernel kernel (orbitCharacter tau) 0 1 (by norm_num)
    (by intro shift; rw [orbitCharacter_norm, pow_zero, one_mul])

theorem kernelOrbit_entryNorm (tau : OrbitParameter) (kernel : FullTwoFrequencyKernel parameters src tgt)
    (shift : ℤ × ℤ) : (kernelOrbit tau kernel).entryNorm shift = kernel.entryNorm shift := by
  apply le_antisymm
  · simpa only [kernelOrbit, pow_zero, one_mul] using
      displacementKernel_entryNorm_le kernel (orbitCharacter tau) 0 1 (by norm_num)
        (by intro shift; rw [orbitCharacter_norm, pow_zero, one_mul]) shift
  · apply kernel.entryNorm_le
    intro input
    have bound := (kernelOrbit tau kernel).entry_le shift input
    change ‖orbitCharacter tau shift • kernel.entry shift input‖ ≤ _ at bound
    simpa only [norm_smul, orbitCharacter_norm, one_mul] using bound

theorem kernelOrbit_moment (tau : OrbitParameter) (kernel : FullTwoFrequencyKernel parameters src tgt)
    (moment : ℕ) : fullKernelMoment parameters moment (kernelOrbit tau kernel) =
      fullKernelMoment parameters moment kernel := by
  unfold fullKernelMoment
  simp only [kernelOrbit_entryNorm]

def orbitJetFactor (tau : OrbitParameter) (angular cell : ℕ) (shift : ℤ × ℤ) : ℂ :=
  (Complex.I * (shift.1 : ℂ)) ^ angular * (Complex.I * (shift.2 : ℂ)) ^ cell * orbitCharacter tau shift

theorem orbitJetFactor_bound (tau : OrbitParameter) (angular cell : ℕ) (shift : ℤ × ℤ) :
    ‖orbitJetFactor tau angular cell shift‖ ≤ 1 * annularFrequency shift.1 shift.2 ^ (angular + cell) := by
  have first : |(shift.1 : ℝ)| ≤ annularFrequency shift.1 shift.2 := by
    unfold annularFrequency; linarith [abs_nonneg (shift.2 : ℝ)]
  have second : |(shift.2 : ℝ)| ≤ annularFrequency shift.1 shift.2 := by
    unfold annularFrequency; linarith [abs_nonneg (shift.1 : ℝ)]
  simp only [orbitJetFactor, norm_mul, norm_pow, Complex.norm_I, one_mul, orbitCharacter_norm, mul_one]
  rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs,
    ← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs, pow_add]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) first angular)
    (pow_le_pow_left₀ (abs_nonneg _) second cell) (pow_nonneg (abs_nonneg _) _)
    (pow_nonneg (annularFrequency_pos shift).le _)

def kernelOrbitJet (tau : OrbitParameter) (angular cell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters src tgt) : FullTwoFrequencyKernel parameters src tgt :=
  displacementKernel kernel (orbitJetFactor tau angular cell) (angular + cell) 1 (by norm_num)
    (orbitJetFactor_bound tau angular cell)

theorem kernelOrbitJet_moment_le (tau : OrbitParameter) (angular cell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters src tgt) (moment : ℕ) :
    fullKernelMoment parameters moment (kernelOrbitJet tau angular cell kernel) ≤
      fullKernelMoment parameters (moment + (angular + cell)) kernel := by
  simpa only [kernelOrbitJet, one_mul] using displacementKernel_moment_le kernel
    (orbitJetFactor tau angular cell) (angular + cell) 1 (by norm_num) (orbitJetFactor_bound tau angular cell) moment

end Grad.AnnularKernelOrbit
