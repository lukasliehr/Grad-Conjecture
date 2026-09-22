import AKV29ExactCartesianPrimitiveSourceRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarRestriction Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.SourceCollarBulk
open Grad.SourceCollarAngular Grad.AnnularSourceGraph Grad.AnnularCurrentSource Grad.AnnularSmoothCore
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation Grad.PhaseAlgebra

def OriginalRowRadialCurves.angular {parameters : PhaseParameters} {lower : ℝ}
    {row target : DivisionRow 1 lower} (curves : OriginalRowRadialCurves parameters lower row)
    (same : ∀ mode : ℤ × ℤ, target mode = (Complex.I*(mode.1 : ℂ)) • row mode) :
    OriginalRowRadialCurves parameters lower target where
  curve grade radius := hilbertFrequencyOperator parameters 1 (some false) (curves.curve (grade+1) radius)
  smooth grade := (hilbertFrequencyOperator parameters 1 (some false)).restrictScalars ℝ |>.contDiff.comp_contDiffOn (curves.smooth (grade+1))
  same grade := by
    have angular : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
        originalRowCoefficient parameters 0 lower target radius mode =
          (Complex.I*(mode.1 : ℂ)) • originalRowCoefficient parameters 0 lower row radius mode := by
      rw [ae_all_iff]
      intro mode
      filter_upwards [Lp.coeFn_smul (Complex.I*(mode.1 : ℂ)) (row mode)] with radius scaled
      unfold originalRowCoefficient
      rw [same mode,scaled]
      exact smul_comm ((originalRowWeight parameters 0 radius mode : ℂ)⁻¹)
        (Complex.I*(mode.1 : ℂ)) (row mode radius)
    filter_upwards [curves.same (grade+1),angular] with radius represented angular
    intro mode
    rw [hilbertFrequencyOperator_apply,represented mode,angular mode]
    have weighted := frequencyRatio_weighted (some false) mode grade
      ((Real.exp (radialPhase parameters radius mode.2) : ℂ) • originalRowCoefficient parameters 0 lower row radius mode)
    simp only [Complex.ofReal_pow] at weighted
    rw [weighted]
    congr 1
    exact smul_comm (Complex.I*(mode.1 : ℂ)) (Real.exp (radialPhase parameters radius mode.2) : ℂ) _

def actualCartesianPrimitiveRows (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (source : SmoothQuotient parameters) : Fin 4 → DivisionRow 1 lower :=
  ![unweightedSourceF0Bulk parameters lower (actualOriginalF0Graph parameters lower positive bounded 0 source),
    unweightedSourceRF0Bulk parameters lower (actualOriginalF0Graph parameters lower positive bounded 0 source),
    unweightedSourceF2Bulk parameters lower (actualOriginalF2Graph parameters length lower positive bounded 0 source),
    actualOriginalF1Row parameters lower positive bounded.le 0 source]

/-- All four actual primitive source rows, with RF0 derived from the same
F0 graph and with the literal original length factor in F2. -/
def actualCartesianPrimitiveRadialCurves (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (source : SmoothQuotient parameters) (slot : Fin 4) :
    OriginalRowRadialCurves parameters lower (actualCartesianPrimitiveRows parameters length lower positive bounded source slot) := by
  have f0 : OriginalRowRadialCurves parameters lower
      (unweightedSourceF0Bulk parameters lower (actualOriginalF0Graph parameters lower positive bounded 0 source)) := by
    rw [actualOriginalF0Bulk_exact parameters lower positive bounded source]
    exact (cartesianOriginalRowRadialCurves parameters lower positive bounded (cartesianSourceVector source)).tangential positive
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun impossible => Fin.elim0 impossible)))) slot
  · exact f0
  · exact f0.angular (unweightedSourceRF0Bulk_same_angular parameters lower _)
  · change OriginalRowRadialCurves parameters lower
      (unweightedSourceF2Bulk parameters lower (actualOriginalF2Graph parameters length lower positive bounded 0 source))
    rw [actualOriginalF2Bulk_exact parameters lower positive bounded source length]
    exact (cartesianOriginalRowRadialCurves parameters lower positive bounded (source 3)).smul ((length : ℂ)⁻¹)
  · change OriginalRowRadialCurves parameters lower (actualOriginalF1Row parameters lower positive bounded.le 0 source)
    rw [actualOriginalF1Bulk_exact parameters lower positive bounded source]
    exact (cartesianOriginalRowRadialCurves parameters lower positive bounded (cartesianSourceVector source)).radial positive

end Grad.AnnularGeneralSourceRegularity
