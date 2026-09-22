import AAR21NaturalMomentBoundary
import AAR22PhysicalContinuousSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Inverse of the original normalization beta ↦ nu^(-1/2) D e^Phi(1) beta. -/
def annularOuterDatum (parameters : PhaseParameters) (mode : HighAnnularMode)
    (normalized : ComplexEuclidean 1) : ComplexEuclidean 1 :=
  (annularDSymbol mode)⁻¹ • (annularInversePhase parameters mode.val.2 1 •
    ((Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) • normalized))

section Outer
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem annularPhysicalQSection_outer (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (mode : HighAnnularMode) :
    annularPhysicalQSection parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode
      ⟨1, bounded.le, le_rfl⟩ =
      -(annularInversePhase parameters mode.val.2 1 •
        ((Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) • source.2.2.2 mode)) := by
  change annularInversePhase parameters mode.val.2 1 •
    ((1 / max lower 1) • weightedRadialSection 1 lower positive bounded
      (annularQMomentGraph parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode)
      ⟨1, bounded.le, le_rfl⟩) = _
  rw [max_eq_right bounded.le, div_one, one_smul]
  have endpoint := weightedRadialSection_endpoint 1 lower positive bounded 1
    (annularQMomentGraph parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode)
  change weightedRadialSection 1 lower positive bounded
    (annularQMomentGraph parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode)
    ⟨1, bounded.le, le_rfl⟩ = _ at endpoint
  rw [endpoint, annularQMomentGraph_outer, smul_neg]

/-- AG24: the actual continuous representative of the genuine weak p
solution has precisely the supplied physical outer value. -/
theorem annularPhysicalPSection_outer (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (mode : HighAnnularMode) :
    annularPhysicalPSection parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode
      ⟨1, bounded.le, le_rfl⟩ = annularOuterDatum parameters mode (source.2.2.2 mode) := by
  change (-(annularDSymbol mode)⁻¹) •
    annularPhysicalQSection parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode
      ⟨1, bounded.le, le_rfl⟩ = _
  rw [annularPhysicalQSection_outer, smul_neg, neg_smul, neg_neg]
  rfl

theorem annularPhysicalPSection_outer_zero (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (mode : HighAnnularMode) (homogeneous : source.2.2.2 = 0) :
    annularPhysicalPSection parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode
      ⟨1, bounded.le, le_rfl⟩ = 0 := by
  rw [annularPhysicalPSection_outer, homogeneous]
  change annularOuterDatum parameters mode 0 = 0
  simp only [annularOuterDatum, smul_zero]

end Outer
end Grad.AnnularReconstruction
