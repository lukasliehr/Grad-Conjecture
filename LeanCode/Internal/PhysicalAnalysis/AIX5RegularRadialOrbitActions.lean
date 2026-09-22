import AIX4ActualKernelUnitaryConjugation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularKernelOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularKernelContinuity

variable {src tgt : ℕ} (parameters : PhaseParameters)
    (kernel : (r : RadialPoint) → RadialKernel parameters r src tgt) (regular : RegularKernelFamily kernel)
include regular

/-- All existing radial entry continuity and uniform moments pass to an
actual polynomial displacement multiplier without altering the physical radius. -/
theorem displacementKernel_regular (scalar : (ℤ × ℤ) → ℂ) (degree : ℕ)
    (constant : ℝ) (nonnegative : 0 ≤ constant)
    (scalarBound : ∀ shift, ‖scalar shift‖ ≤ constant * annularFrequency shift.1 shift.2 ^ degree) :
    RegularKernelFamily (fun r => displacementKernel (kernel r) scalar degree constant nonnegative scalarBound) := by
  constructor
  · intro shift input
    change Continuous (fun r => scalar shift • (kernel r).entry shift input)
    exact (continuous_const : Continuous (fun _ : RadialPoint => scalar shift)).smul (regular.1 shift input)
  · intro moment
    obtain ⟨bound, boundNonnegative, boundLaw⟩ := regular.2 (moment + degree)
    refine ⟨constant * bound, mul_nonneg nonnegative boundNonnegative, ?_⟩
    intro radius
    exact (displacementKernel_moment_le (kernel radius) scalar degree constant nonnegative scalarBound moment).trans
      (mul_le_mul_of_nonneg_left (boundLaw radius) nonnegative)

theorem kernelOrbit_regular (tau : OrbitParameter) :
    RegularKernelFamily (fun r => kernelOrbit tau (kernel r)) :=
  displacementKernel_regular parameters kernel regular (orbitCharacter tau) 0 1 (by norm_num)
    (by intro shift; rw [orbitCharacter_norm, pow_zero, one_mul])

theorem kernelOrbitJet_regular (tau : OrbitParameter) (angular cell : ℕ) :
    RegularKernelFamily (fun r => kernelOrbitJet tau angular cell (kernel r)) :=
  displacementKernel_regular parameters kernel regular (orbitJetFactor tau angular cell) (angular + cell) 1
    (by norm_num) (orbitJetFactor_bound tau angular cell)

def radialOrbitAction (power : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (tau : OrbitParameter) : DivisionRow src lower →L[ℂ] DivisionRow tgt lower :=
  regularRadialBulkAction parameters power lower positive bounded
    (fun r => kernelOrbit tau (kernel r)) (kernelOrbit_regular parameters kernel regular tau)

def radialOrbitJetAction (power : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (tau : OrbitParameter) (angular cell : ℕ) : DivisionRow src lower →L[ℂ] DivisionRow tgt lower :=
  regularRadialBulkAction parameters power lower positive bounded
    (fun r => kernelOrbitJet tau angular cell (kernel r)) (kernelOrbitJet_regular parameters kernel regular tau angular cell)

/-- The original AHT completed action with any valid uniform moment witness. -/
theorem regularAction_norm_le (power : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (constant : ℝ) (nonnegative : 0 ≤ constant)
    (momentBound : ∀ r, fullKernelMoment (radialKernelParameters parameters r) power (kernel r) ≤ constant) :
    ‖regularRadialBulkAction parameters power lower positive bounded kernel regular‖ ≤ constant := by
  apply ContinuousLinearMap.opNorm_le_bound _ nonnegative
  intro field
  rw [regularRadialBulkAction_eq_completed parameters power lower positive bounded kernel regular
    (regularRadialBulk_measurable parameters lower positive bounded kernel regular) constant
      (Eventually.of_forall (fun x => momentBound (collarRadius lower positive bounded x)))]
  exact completedBulkKernel_bound _ _ _ _ _ _ _ _ _ field

/-- Uniform in the inner radius; the next mixed envelope moment is the only cost. -/
theorem radialOrbitJetAction_norm_le (power : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (tau : OrbitParameter) (angular cell : ℕ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (momentBound : ∀ r, fullKernelMoment (radialKernelParameters parameters r) (power + (angular + cell)) (kernel r) ≤ constant) :
    ‖radialOrbitJetAction parameters kernel regular power lower positive bounded tau angular cell‖ ≤ constant :=
  regularAction_norm_le parameters (fun r => kernelOrbitJet tau angular cell (kernel r))
    (kernelOrbitJet_regular parameters kernel regular tau angular cell) power lower positive bounded constant nonnegative
    (fun radius => (kernelOrbitJet_moment_le tau angular cell (kernel radius) power).trans (momentBound radius))

end Grad.AnnularKernelOrbit
