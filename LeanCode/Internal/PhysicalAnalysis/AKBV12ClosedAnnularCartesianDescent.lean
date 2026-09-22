import AKBV11PeriodicClosedCylinder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter
open scoped ContDiff Topology
namespace Grad.CartesianCoreRecovery
open Grad.ClosedJets Grad.CartesianState Grad.ActualCartesianDescent Grad.DiskExtension.Operator Grad.Constraints Grad.BoundaryLift
open Grad.ActualSmoothPhysicalField Grad.SourceCollarDivision Grad.AnnularClosedJointRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cartesianFromPolar_smooth_closed (field : ℝ × (ℝ × ℝ) → E) (lower : ℝ) (positive : 0 < lower)
    (smooth : ContDiffOn ℝ ∞ field (Icc lower 1 ×ˢ (univ : Set (ℝ × ℝ))))
    (periodic : ∀ radius axial, Function.Periodic (fun polar => field (radius,polar,axial)) (2*Real.pi)) :
    ContDiffOn ℝ ∞ (cartesianFromPolar field) {point : ℂ × ℝ | ‖point.1‖ ∈ Icc lower 1} := by
  intro point inside
  have nonzero : point.1 ≠ 0 := norm_pos_iff.mp (positive.trans_le inside.1)
  have normSmooth : ContDiffAt ℝ ∞ (fun source : ℂ × ℝ => ‖source.1‖) point :=
    (contDiffAt_norm ℝ nonzero).comp point contDiffAt_fst
  have atField (angle : ℝ) : ContDiffWithinAt ℝ ∞ field
      (Icc lower 1 ×ˢ (univ : Set (ℝ × ℝ))) (‖point.1‖,angle,point.2) := smooth _ ⟨inside,mem_univ _⟩
  by_cases slit : point.1 ∈ Complex.slitPlane
  · have maps : MapsTo (fun source : ℂ × ℝ => (‖source.1‖,Complex.arg source.1,source.2))
        {source : ℂ × ℝ | ‖source.1‖ ∈ Icc lower 1} (Icc lower 1 ×ˢ (univ : Set (ℝ × ℝ))) :=
        fun _ member => ⟨member,mem_univ _⟩
    exact (atField (Complex.arg point.1)).comp point
      (normSmooth.prodMk (((complexArgument_smoothAt point.1 slit).comp point contDiffAt_fst).prodMk
        contDiffAt_snd)).contDiffWithinAt maps
  · have negativeSlit : -point.1 ∈ Complex.slitPlane := by
      change ¬(0 < point.1.re ∨ point.1.im ≠ 0) at slit
      change 0 < (-point.1).re ∨ (-point.1).im ≠ 0
      have imaginary : point.1.im = 0 := (not_or.mp slit).2 |> not_not.mp
      have realNonzero : point.1.re ≠ 0 := by
        intro realZero
        exact nonzero (Complex.ext realZero imaginary)
      left
      simpa only [Complex.neg_re] using neg_pos.mpr
        (lt_of_le_of_ne (le_of_not_gt (not_or.mp slit).1) realNonzero)
    have angleSmooth : ContDiffAt ℝ ∞ (fun source : ℂ × ℝ => Complex.arg (-source.1)+Real.pi) point :=
      ((complexArgument_smoothAt (-point.1) negativeSlit).comp point contDiffAt_fst.neg).add contDiffAt_const
    have maps : MapsTo (fun source : ℂ × ℝ => (‖source.1‖,Complex.arg (-source.1)+Real.pi,source.2))
        {source : ℂ × ℝ | ‖source.1‖ ∈ Icc lower 1} (Icc lower 1 ×ˢ (univ : Set (ℝ × ℝ))) :=
        fun _ member => ⟨member,mem_univ _⟩
    have localSmooth : ContDiffWithinAt ℝ ∞
        (fun source : ℂ × ℝ => field (‖source.1‖,Complex.arg (-source.1)+Real.pi,source.2))
        {source : ℂ × ℝ | ‖source.1‖ ∈ Icc lower 1} point :=
      (atField (Complex.arg (-point.1)+Real.pi)).comp point
        (normSmooth.prodMk (angleSmooth.prodMk contDiffAt_snd)).contDiffWithinAt
        maps
    apply localSmooth.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with source member
      exact (periodic_arg_negative (fun angle => field (‖source.1‖,angle,source.2))
        (periodic ‖source.1‖ source.2) source.1 (norm_pos_iff.mp (positive.trans_le member.1))).symm
    · exact (periodic_arg_negative (fun angle => field (‖point.1‖,angle,point.2))
        (periodic ‖point.1‖ point.2) point.1 nonzero).symm

theorem cartesianPhysicalField_smooth_closed (field : ℝ × (ℝ × ℝ) → E) (lower : ℝ) (positive : 0 < lower)
    (smooth : ContDiffOn ℝ ∞ field (Icc lower 1 ×ˢ (univ : Set (ℝ × ℝ))))
    (periodic : ∀ radius axial, Function.Periodic (fun polar => field (radius,polar,axial)) (2*Real.pi)) :
    ContDiffOn ℝ ∞ (cartesianPhysicalField field) {point : SpatialPlane × ℝ | ‖point.1‖ ∈ Icc lower 1} := by
  apply (cartesianFromPolar_smooth_closed field lower positive smooth periodic).comp
    ((((signedComplexCoordinate_smooth 1).comp contDiff_fst).prodMk contDiff_snd).contDiffOn)
  intro point member
  change ‖signedComplexCoordinate 1 point.1‖ ∈ Icc lower 1
  rw [complexCoordinate_norm]
  exact member

def weightedCartesianField {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1) : SpatialPlane × ℝ → ComplexEuclidean dimension :=
  cartesianPhysicalField (weightedFullField curves bounded)

theorem weightedCartesianField_smooth_closed {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1) :
    ContDiffOn ℝ ∞ (weightedCartesianField curves bounded) {point : SpatialPlane × ℝ | ‖point.1‖ ∈ Icc lower 1} :=
  cartesianPhysicalField_smooth_closed _ lower positive (weightedFullField_smooth curves bounded)
    (weightedFullField_angular_periodic curves bounded)

end Grad.CartesianCoreRecovery
