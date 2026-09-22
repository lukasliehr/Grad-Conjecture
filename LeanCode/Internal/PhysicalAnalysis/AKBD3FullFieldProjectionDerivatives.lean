import AKBD2ProjectedParameterCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualDeterminantEquations
open Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource Grad.Constraints

variable {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℂ Value]

/-- P commutes with the genuine radial derivative on an open collar; its
compact angular integral is differentiated by the existing analytic theorem. -/
theorem removePolarMean_radial_hasDerivAt (field : ℝ × (ℝ × ℝ) → Value) (lower upper : ℝ)
    (smooth : ContDiffOn ℝ ∞ field (Ioo lower upper ×ˢ (univ : Set (ℝ × ℝ))))
    (radius : ℝ) (inside : radius ∈ Ioo lower upper) (polar axial : ℝ)
    (slope : ℝ → Value)
    (derivative : ∀ angle, HasDerivAt (fun value => field (value,angle,axial)) (slope angle) radius) :
    HasDerivAt (fun value => removePolarMean (fun angles => field (value,angles)) (polar,axial))
      (slope polar-angularCoefficient slope 0) radius := by
  have sectionSmooth : ContDiffOn ℝ ∞ (fun point : ℝ × ℝ => field (point.1,point.2,axial))
      (Ioo lower upper ×ˢ univ) :=
    smooth.comp (contDiffOn_fst.prodMk (contDiffOn_snd.prodMk contDiffOn_const))
      (fun point member => ⟨member.1,mem_univ _⟩)
  have meanDerivative := angularMean_hasDerivAt_on (fun point : ℝ × ℝ => field (point.1,point.2,axial))
    (Ioo lower upper) isOpen_Ioo sectionSmooth radius inside slope derivative
  simpa only [removePolarMean,Pi.sub_def] using (derivative polar).sub meanDerivative

/-- P commutes with the genuine axial derivative of the SAME field. -/
theorem removePolarMean_axial_hasDerivAt (field : ℝ × ℝ → Value)
    (smooth : ContDiff ℝ ∞ field) (polar axial : ℝ) (slope : ℝ → Value)
    (derivative : ∀ angle, HasDerivAt (fun value => field (angle,value)) (slope angle) axial) :
    HasDerivAt (fun value => removePolarMean field (polar,value))
      (slope polar-angularCoefficient slope 0) axial := by
  have sectionSmooth : ContDiffOn ℝ ∞ (fun point : ℝ × ℝ => field (point.2,point.1))
      ((univ : Set ℝ) ×ˢ univ) := (smooth.comp (contDiff_snd.prodMk contDiff_fst)).contDiffOn
  have meanDerivative := angularMean_hasDerivAt_on (fun point : ℝ × ℝ => field (point.2,point.1))
    univ isOpen_univ sectionSmooth axial (mem_univ _) slope derivative
  simpa only [removePolarMean,Pi.sub_def] using (derivative polar).sub meanDerivative

end Grad.ActualDeterminantEquations
