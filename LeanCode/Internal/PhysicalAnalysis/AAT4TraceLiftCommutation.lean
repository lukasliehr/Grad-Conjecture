import AAT3CoordinateCommutation

noncomputable section
set_option maxHeartbeats 800000

open scoped Topology

namespace Grad.AnnularGrades

open Grad.AnnularVariational Grad.ClosedJets

section Boundary
variable (lower length : ℝ) (positive : 0 < lower) (collar : lower < 1) (lengthPositive : 0 < length)
    (coefficient : HighAnnularMode → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ index, |coefficient index| ≤ constant)

theorem finiteAnnularTraceCore_diagonal (endpoint : Fin 2)
    (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    finiteAnnularTraceCore lower endpoint (finiteRealDiagonal coefficient core) =
      realLpDiagonal coefficient constant nonnegative bounded (finiteAnnularTraceCore lower endpoint core) := by
  apply lp.ext
  funext mode
  rw [finiteAnnularTraceCore_apply, realLpDiagonal_apply, finiteAnnularTraceCore_apply,
    finiteRealDiagonal_apply]
  change (Real.sqrt (annularFrequency mode.val.1 mode.val.2) : ℂ) •
    ((coefficient mode : ℂ) • (core mode).val.1 (Grad.AnnularSourceGraph.radialEndpointRadius lower endpoint)) = _
  exact smul_comm _ _ _

/-- Both sharp physical trace coordinates commute with the same Fourier
multiplier; the identity is extended from the actual dense smooth core. -/
theorem annularEnergyTrace_diagonal (endpoint : Fin 2) (field : annularEnergySpace lower length positive) :
    annularEnergyTrace lower length positive collar lengthPositive endpoint
      (annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded field) =
        realLpDiagonal coefficient constant nonnegative bounded
          (annularEnergyTrace lower length positive collar lengthPositive endpoint field) := by
  apply isClosed_property (annularEnergyCoreInto_denseRange lower length positive)
    (isClosed_eq
      ((annularEnergyTrace lower length positive collar lengthPositive endpoint).continuous.comp
        (annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded).continuous)
      ((realLpDiagonal coefficient constant nonnegative bounded).continuous.comp
        (annularEnergyTrace lower length positive collar lengthPositive endpoint).continuous)) _ field
  intro core
  simp only [Function.comp_apply]
  rw [annularEnergyDiagonal_core, annularEnergyTrace_core, annularEnergyTrace_core]
  exact finiteAnnularTraceCore_diagonal lower coefficient constant nonnegative bounded endpoint core

theorem annularInnerLift_diagonal (boundary : AnnularBoundary) :
    annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded
      (annularInnerLift lower length positive collar boundary) =
        annularInnerLift lower length positive collar
          (realLpDiagonal coefficient constant nonnegative bounded boundary) := by
  apply Subtype.ext
  apply lp.ext
  funext mode
  rw [annularEnergyDiagonal_apply]
  change (coefficient mode : ℂ) • (annularInnerLiftRaw lower length positive collar boundary mode) =
    annularInnerLiftRaw lower length positive collar (realLpDiagonal coefficient constant nonnegative bounded boundary) mode
  simp only [annularInnerLiftRaw_apply, realLpDiagonal_apply, map_smul]

theorem annularInnerZero_diagonal (field : annularInnerZero lower length positive collar lengthPositive) :
    annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded field.val ∈
      annularInnerZero lower length positive collar lengthPositive := by
  change annularEnergyTrace lower length positive collar lengthPositive 0
    (annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded field.val) = 0
  rw [annularEnergyTrace_diagonal]
  have zero : annularEnergyTrace lower length positive collar lengthPositive 0 field.val = 0 := field.property
  rw [zero, map_zero]

def annularZeroDiagonal : annularInnerZero lower length positive collar lengthPositive →L[ℂ]
    annularInnerZero lower length positive collar lengthPositive :=
  ((annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded).comp
    (annularInnerZero lower length positive collar lengthPositive).subtypeL).codRestrict _
      (annularInnerZero_diagonal lower length positive collar lengthPositive coefficient constant nonnegative bounded)

end Boundary

end Grad.AnnularGrades
