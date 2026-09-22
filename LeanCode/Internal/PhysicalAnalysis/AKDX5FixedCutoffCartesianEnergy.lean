import AKDX4FixedCartesianEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.OriginalCollarNorm
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints Grad.BoundaryLift
open Grad.DiskExtension.Operator

theorem exists_fixedPolarCutoffBound (lower : ℝ) (cutoff : ℝ × ℝ→ℝ)
    (smooth : ContDiff ℝ ∞ cutoff) (grade : ℕ) :
    ∃ bound : ℝ,0≤bound ∧ ∀ order,order≤grade → ∀ point∈fixedCollarRectangle lower,
      ‖iteratedFDeriv ℝ order cutoff point‖≤bound := by
  have continuousEnvelope : Continuous (polarJetEnvelope cutoff grade) := by
    apply continuous_finsetSum
    intro order _
    exact (smooth.continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (order : ℕ∞)≤⊤))).norm
  obtain ⟨bound,property⟩ := bddAbove_def.mp
    ((isCompact_Icc.prod isCompact_Icc).bddAbove_image continuousEnvelope.continuousOn)
  refine ⟨max 0 bound,le_max_left _ _,?_⟩
  intro order upper point inside
  exact (polarJetEnvelope_bound cutoff grade order upper point).trans
    ((property _ ⟨point,inside,rfl⟩).trans (le_max_right _ _))

/-- One fixed-cutoff constant controls every physical Cartesian row by
the genuine polar derivative energy, uniformly in the field and dimension. -/
theorem fixedCutoff_cartesian_energy (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (cutoff : SpatialPlane→ℝ) (cutoffSmooth : ContDiff ℝ ∞ cutoff)
    (vanishes : ∀ point,‖point‖<2*lower → cutoff point=0) (index : CartesianMultiIndex) :
    ∃ constant : ℝ,0≤constant ∧ ∀ dimension (field : SpatialPlane→ComplexEuclidean dimension)
      (smooth : ContDiff ℝ ∞ field),
      ‖closedDerivativeL2 index (globalClosedJet (fun point => cutoff point • field point)
        (cutoffSmooth.smul smooth))‖^2≤constant*fixedCollarIntegral lower
          (polarJetSquaredDensity (field ∘ collarPlane) (cartesianOrder index)) := by
  let grade := cartesianOrder index
  let polarCutoff := cutoff ∘ collarPlane
  have polarSmooth : ContDiff ℝ ∞ polarCutoff := cutoffSmooth.comp collarPlane_smooth
  obtain ⟨bound,bound0,cutoffBounds⟩ := exists_fixedPolarCutoffBound lower polarCutoff polarSmooth grade
  refine ⟨fixedReverseConstant lower positive grade*Grad.CollarCartesian.cutoffDensityConstant bound grade,
    mul_nonneg (fixedReverseConstant_nonnegative lower positive grade)
      (Grad.CollarCartesian.cutoffDensityConstant_nonnegative bound grade),?_⟩
  intro dimension field smooth
  have first := closedDerivative_fixedCollar_energy lower positive bounded
    (fun point => cutoff point • field point) (cutoffSmooth.smul smooth)
    (fun point inside => by rw [vanishes point inside,zero_smul]) index
  have comparison := fixedCollarIntegral_mono lower bounded
    (polarJetSquaredDensity (fun point => polarCutoff point • (field ∘ collarPlane) point) grade)
    (fun point => Grad.CollarCartesian.cutoffDensityConstant bound grade*
      polarJetSquaredDensity (field ∘ collarPlane) grade point)
    (polarJetSquaredDensity_continuous _ (polarSmooth.smul (smooth.comp collarPlane_smooth)) grade)
    (continuous_const.mul (polarJetSquaredDensity_continuous _ (smooth.comp collarPlane_smooth) grade))
    (fun point inside => Grad.CollarCartesian.cutoff_density_bound polarCutoff polarSmooth
      (field ∘ collarPlane) (smooth.comp collarPlane_smooth) grade bound bound0 point
      (fun order upper => cutoffBounds order upper point inside))
  rw [fixedCollarIntegral_const_mul] at comparison
  exact (first.trans (mul_le_mul_of_nonneg_left comparison
    (fixedReverseConstant_nonnegative lower positive grade))).trans_eq (mul_assoc _ _ _).symm

end Grad.OriginalCollarNorm
