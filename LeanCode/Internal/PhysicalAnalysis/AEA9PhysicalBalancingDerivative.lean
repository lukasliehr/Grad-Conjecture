import AEA7UniformNormalizedCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularLowReference
open Grad.AnnularLowEnergy Grad.AnnularVariational Grad.PhaseAlgebra
open Grad.CartesianState

def lowBalancingLogSlope (parameters : PhaseParameters) (length radius : ℝ)
    (mode : LowAnnularMode) (entry : Fin 2) : ℝ :=
  annularPhaseSlope parameters mode.val.2 radius +
    if entry = 0 then lowMuLogSlope length radius mode.val.2 else 0

/-- Genuine product differentiation of the original curved phase and BE2 multiplier. -/
theorem lowPhysicalFactor_hasDerivAt (parameters : PhaseParameters) (length radius : ℝ)
    (mode : LowAnnularMode) (positive : 0 < radius) (entry : Fin 2) :
    HasDerivAt (fun point => lowPhysicalFactor parameters length point (entry, mode))
      (lowPhysicalFactor parameters length radius (entry, mode) *
        lowBalancingLogSlope parameters length radius mode entry) radius := by
  have phase := (radialPhase_hasDerivAt parameters mode.val.2 radius).exp
  fin_cases entry
  · change HasDerivAt (fun point => Real.exp (radialPhase parameters point mode.val.2) *
      (lowAmplitude length parameters.gamma mode * lowMu length point mode.val.2))
      ((Real.exp (radialPhase parameters radius mode.val.2) *
        (lowAmplitude length parameters.gamma mode * lowMu length radius mode.val.2)) *
        (annularPhaseSlope parameters mode.val.2 radius + lowMuLogSlope length radius mode.val.2)) radius
    have muDerivative := (lowMu_hasDerivAt length radius mode.val.2 positive).const_mul (lowAmplitude length parameters.gamma mode)
    have equality : (Real.exp (radialPhase parameters radius mode.val.2) *
        (lowAmplitude length parameters.gamma mode * lowMu length radius mode.val.2)) *
        (annularPhaseSlope parameters mode.val.2 radius + lowMuLogSlope length radius mode.val.2) =
      (Real.exp (radialPhase parameters radius mode.val.2) * annularPhaseSlope parameters mode.val.2 radius) *
        (lowAmplitude length parameters.gamma mode * lowMu length radius mode.val.2) +
      Real.exp (radialPhase parameters radius mode.val.2) *
        (lowAmplitude length parameters.gamma mode * lowMuSlope length radius mode.val.2) := by
      unfold lowMuLogSlope lowMuSlope
      field_simp [(lowMu_pos length radius mode.val.2 positive).ne']
    rw [equality]
    exact phase.mul muDerivative
  · simpa [lowPhysicalFactor, lowBalancingLogSlope] using phase

/-- Multiplying the entrywise conjugation back by its physical input factor
keeps the exact diagonal derivative contribution and cancels no source row. -/
theorem lowReferenceMatrix_physical_factor (parameters : PhaseParameters) (length radius : ℝ)
    (mode : LowAnnularMode) (positive : 0 < radius) (row column : Fin 2) :
    lowReferenceMatrix parameters length radius mode row column * lowPhysicalFactor parameters length radius (column, mode) =
      lowPhysicalFactor parameters length radius (row, mode) * lowCircularMatrix length radius mode row column +
      if row = column then lowPhysicalFactor parameters length radius (row, mode) *
        lowBalancingLogSlope parameters length radius mode row else 0 := by
  rw [lowReferenceMatrix_conjugation parameters length radius mode positive row column]
  have factor (entry : Fin 2) : lowPhysicalFactor parameters length radius (entry, mode) =
      Real.exp (radialPhase parameters radius mode.val.2) * lowConjugatingEntry length parameters.gamma radius mode entry := rfl
  rw [factor, factor]
  by_cases same : row = column
  · subst column
    rw [if_pos rfl, if_pos rfl]
    have slope : lowBalancingLogSlope parameters length radius mode row =
        annularPhaseSlope parameters mode.val.2 radius + if row = 0 then lowMuLogSlope length radius mode.val.2 else 0 := rfl
    rw [slope]
    simp only [and_self]
    field_simp [(lowConjugatingEntry_pos length parameters.gamma radius mode positive row).ne']
    ring
  · rw [if_neg same, if_neg same]
    have different : ¬ (row = 0 ∧ column = 0) := by rintro ⟨rfl, rfl⟩; exact same rfl
    rw [if_neg different]
    field_simp [(lowConjugatingEntry_pos length parameters.gamma radius mode positive column).ne']
    ring

end Grad.AnnularLowReference
