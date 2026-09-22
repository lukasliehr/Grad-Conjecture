import AFI1ActualInteriorReconstruction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualReferenceAssembly
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.GaugeCoefficients.Envelope
open Grad.BoundaryTrace Grad.CircularHighWeak
open Grad.ActualScalarForcing Grad.ActualScalarResidual
variable {L sigma gamma ell : ℝ}

theorem originalBoundary_ext (grade : ℕ) {first second : APBoundaryGrade L sigma gamma ell 1 grade}
    (same : ∀ pair, apBoundaryCoefficient L sigma gamma ell grade first pair =
      apBoundaryCoefficient L sigma gamma ell grade second pair) : first = second := by
  apply lp.ext
  funext pair
  exact (apBoundary_weighted_coefficient L sigma gamma ell grade first pair).symm.trans
    ((congrArg (fun value => (apBoundaryWeight L sigma gamma ell grade pair : ℂ) • value) (same pair)).trans
      (apBoundary_weighted_coefficient L sigma gamma ell grade second pair))

theorem highMode_not_low (mode : ℤ) (high : 3 ≤ |mode|) : mode ∉ lowAngularModes := by
  intro member
  simp only [lowAngularModes, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> norm_num at high

theorem not_highMode_low (mode : ℤ) (low : ¬ 3 ≤ |mode|) : mode ∈ lowAngularModes := by
  have bounded : |mode| ≤ 2 := by omega
  have bounds := abs_le.mp bounded
  simp only [lowAngularModes, Finset.mem_insert, Finset.mem_singleton]
  omega

theorem highMultiplier_complex (mode : ℤ) (high : 3 ≤ |mode|) :
    (highMultiplier mode : ℂ) = 1 - 4 / (mode : ℂ) ^ 2 := by
  rw [highMultiplier_high mode (highMode_not_low mode high)]
  push_cast
  rfl

theorem boundaryB_highProjection (grade : ℕ) (field : APBoundaryGrade L sigma gamma ell 1 grade) :
    boundaryB L sigma gamma ell grade (apHighProjection L sigma gamma ell grade field) =
      boundaryB L sigma gamma ell grade field := by
  apply lp.ext
  funext pair
  rw [boundaryB_apply, apHighProjection_apply, boundaryB_apply]
  by_cases high : 3 ≤ |pair.1|
  · rw [if_pos high]
  · rw [if_neg high, smul_zero, highMultiplier, if_pos (not_highMode_low pair.1 high)]
    simp only [Complex.ofReal_zero, zero_smul]

theorem boundaryB_high (grade : ℕ) (field : APBoundaryGrade L sigma gamma ell 1 grade) :
    apHighProjection L sigma gamma ell grade (boundaryB L sigma gamma ell grade field) =
      boundaryB L sigma gamma ell grade field := by
  apply lp.ext
  funext pair
  rw [apHighProjection_apply]
  by_cases high : 3 ≤ |pair.1|
  · rw [if_pos high]
  · rw [if_neg high, boundaryB_low grade field pair (not_highMode_low pair.1 high)]

theorem boundaryB_high_injective (grade : ℕ) (first second : APBoundaryGrade L sigma gamma ell 1 grade)
    (firstHigh : apHighProjection L sigma gamma ell grade first = first)
    (secondHigh : apHighProjection L sigma gamma ell grade second = second)
    (same : boundaryB L sigma gamma ell grade first = boundaryB L sigma gamma ell grade second) : first = second := by
  apply lp.ext
  funext pair
  by_cases high : 3 ≤ |pair.1|
  · have nonzero : (highMultiplier pair.1 : ℂ) ≠ 0 := by
      apply Complex.ofReal_ne_zero.mpr
      have bound := (highMultiplier_bounds pair.1 (highMode_not_low pair.1 high)).1
      linarith
    have equation := congrArg (fun field : APBoundaryGrade L sigma gamma ell 1 grade => field pair) same
    exact (smul_right_injective _ nonzero) equation
  · have firstZero := congrArg (fun field : APBoundaryGrade L sigma gamma ell 1 grade => field pair) firstHigh
    have secondZero := congrArg (fun field : APBoundaryGrade L sigma gamma ell 1 grade => field pair) secondHigh
    rw [apHighProjection_apply, if_neg high] at firstZero secondZero
    exact firstZero.symm.trans secondZero

/-- The actual full disk multiplier commutes with the original high trace.
Both sides have the same physical Fourier coefficients at the same AP grade. -/
theorem fullB_highTrace (admissible : Admissible L sigma gamma ell) (grade : ℕ) (positive : 1 ≤ grade)
    (field : APSmooth L sigma gamma ell 1) :
    apHighTrace L sigma gamma ell grade positive (apSmoothGrade L sigma gamma ell 1 grade (apFullB admissible field)) =
      boundaryB L sigma gamma ell grade
        (apBoundaryTrace L sigma gamma ell grade positive (apSmoothGrade L sigma gamma ell 1 grade field)) := by
  apply originalBoundary_ext grade
  intro pair
  have left := apHighProjection_coefficient L sigma gamma ell grade
    (apBoundaryTrace L sigma gamma ell grade positive (apSmoothGrade L sigma gamma ell 1 grade (apFullB admissible field))) pair
  have right := (boundaryB_coefficient grade _ pair).trans
    (congrArg (fun value => (highMultiplier pair.1 : ℂ) • value)
      (originalSmoothTrace_coefficient admissible grade positive field pair))
  by_cases high : 3 ≤ |pair.1|
  · rw [if_pos high] at left
    have modeNonzero : pair.1 ≠ 0 := by intro zero; rw [zero] at high; norm_num at high
    have coefficient := (congrArg (angularClosedJet pair.1) (apFullB_jet admissible field pair.2)).trans
      ((literalMultiplier_coefficient pair.1 (apSmoothJet admissible 1 pair.2 field)).trans (if_neg modeNonzero))
    have evaluated := congrArg (fun jet : ClosedJet 1 => jet.value (boundaryDiskPoint 0)) coefficient
    have scalarEquality := highMultiplier_complex pair.1 high
    exact left.trans ((originalSmoothTrace_coefficient admissible grade positive (apFullB admissible field) pair).trans
      (evaluated.trans ((congrArg (fun coefficient : ℂ => coefficient •
        (angularClosedJet pair.1 (apSmoothJet admissible 1 pair.2 field)).value (boundaryDiskPoint 0)) scalarEquality.symm).trans right.symm)))
  · rw [if_neg high] at left
    have zero : (highMultiplier pair.1 : ℂ) = 0 := by
      rw [highMultiplier, if_pos (not_highMode_low pair.1 high)]
      rfl
    have coefficientZero : (highMultiplier pair.1 : ℂ) •
        (angularClosedJet pair.1 (apSmoothJet admissible 1 pair.2 field)).value (boundaryDiskPoint 0) = 0 :=
      (congrArg (fun coefficient : ℂ => coefficient •
        (angularClosedJet pair.1 (apSmoothJet admissible 1 pair.2 field)).value (boundaryDiskPoint 0)) zero).trans (zero_smul ℂ _)
    exact left.trans (right.trans coefficientZero).symm

end Grad.ActualReferenceAssembly
