import SCD27RadialSeparation

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState

/-- Every derivative coordinate is uniquely determined by the zeroth
coordinate. Thus this closed graph has no independent derivative data. -/
theorem annularDerivativeGraph_ext {dimension radial : ℕ} {lower : ℝ} {positive : 0 < lower}
    (first second : annularDerivativeGraph dimension lower positive radial)
    (sameValue : first.val 0 = second.val 0) : first = second := by
  apply Subtype.ext
  apply PiLp.ext
  intro index
  induction index using Fin.induction with
  | zero => exact sameValue
  | succ index previous =>
    apply lp.ext
    funext mode
    have firstLaw := (annularDerivativeGraph_mem_iff lower positive radial first.val).mp first.property index mode
    have secondLaw := (annularDerivativeGraph_mem_iff lower positive radial second.val).mp second.property index mode
    rw [previous] at firstLaw
    exact firstLaw.unique secondLaw

def annularValue (dimension : ℕ) (lower : ℝ) (positive : 0 < lower) (radial : ℕ) :
    annularDerivativeGraph dimension lower positive radial →L[ℂ] DivisionRow dimension lower :=
  (PiLp.proj 1 (fun _ : Fin (radial + 1) => DivisionRow dimension lower) 0).comp
    (annularDerivativeGraph dimension lower positive radial).subtypeL

theorem annularValue_injective (dimension : ℕ) (lower : ℝ) (positive : 0 < lower) (radial : ℕ) :
    Function.Injective (annularValue dimension lower positive radial) :=
  fun first second same => annularDerivativeGraph_ext first second same

end Grad.SourceCollarDivision
