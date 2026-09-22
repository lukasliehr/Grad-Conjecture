import AEA11OriginalPhysicalEnergyConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat
namespace Grad.AnnularLowVolterra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def curveExtension (lower upper : ℝ) (ordered : lower ≤ upper)
    (curve : C(Icc lower upper, E)) (radius : ℝ) : E :=
  curve (projIcc lower upper ordered radius)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem curveExtension_continuous (lower upper : ℝ) (ordered : lower ≤ upper)
    (curve : C(Icc lower upper, E)) : Continuous (curveExtension lower upper ordered curve) :=
  curve.continuous.comp continuous_projIcc

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem curveExtension_of_mem (lower upper : ℝ) (ordered : lower ≤ upper)
    (curve : C(Icc lower upper, E)) (radius : ℝ) (member : radius ∈ Icc lower upper) :
    curveExtension lower upper ordered curve radius = curve ⟨radius, member⟩ := by
  rw [curveExtension, projIcc_of_mem]

def volterraIntegrand (lower upper : ℝ) (ordered : lower ≤ upper)
    (coefficient : C(Icc lower upper, E →L[ℝ] E)) (source curve : C(Icc lower upper, E))
    (radius : ℝ) : E :=
  coefficient (projIcc lower upper ordered radius) (curveExtension lower upper ordered curve radius) +
    curveExtension lower upper ordered source radius

omit [CompleteSpace E] in
theorem volterraIntegrand_continuous (lower upper : ℝ) (ordered : lower ≤ upper)
    (coefficient : C(Icc lower upper, E →L[ℝ] E)) (source curve : C(Icc lower upper, E)) :
    Continuous (volterraIntegrand lower upper ordered coefficient source curve) :=
  ((coefficient.continuous.comp continuous_projIcc).clm_apply
    (curveExtension_continuous lower upper ordered curve)).add
      (curveExtension_continuous lower upper ordered source)

/-- The Picard map on the complete space of ALL continuous curves on the
whole interval. No local state ball or pre-existing solution is assumed. -/
def volterraNext (lower upper : ℝ) (ordered : lower ≤ upper)
    (coefficient : C(Icc lower upper, E →L[ℝ] E)) (source : C(Icc lower upper, E))
    (initial : E) (curve : C(Icc lower upper, E)) : C(Icc lower upper, E) where
  toFun point := initial + ∫ radius in lower..point.val,
    volterraIntegrand lower upper ordered coefficient source curve radius
  continuous_toFun := continuous_const.add
    ((intervalIntegral.differentiable_integral_of_continuous
      (volterraIntegrand_continuous lower upper ordered coefficient source curve)).continuous.comp
        continuous_subtype_val)

theorem volterraNext_apply (lower upper : ℝ) (ordered : lower ≤ upper)
    (coefficient : C(Icc lower upper, E →L[ℝ] E)) (source : C(Icc lower upper, E))
    (initial : E) (curve : C(Icc lower upper, E)) (point : Icc lower upper) :
    volterraNext lower upper ordered coefficient source initial curve point =
      initial + ∫ radius in lower..point.val,
        volterraIntegrand lower upper ordered coefficient source curve radius := rfl

theorem volterraNext_initial (lower upper : ℝ) (ordered : lower ≤ upper)
    (coefficient : C(Icc lower upper, E →L[ℝ] E)) (source : C(Icc lower upper, E))
    (initial : E) (curve : C(Icc lower upper, E)) :
    volterraNext lower upper ordered coefficient source initial curve ⟨lower, le_rfl, ordered⟩ = initial := by
  simp only [volterraNext_apply, integral_same, add_zero]

omit [CompleteSpace E] in
theorem volterraIntegrand_dist_bound (lower upper : ℝ) (ordered : lower ≤ upper)
    (coefficient : C(Icc lower upper, E →L[ℝ] E)) (source first second : C(Icc lower upper, E))
    (bound : ℝ≥0) (bounded : ∀ point, ‖coefficient point‖ ≤ bound) (radius : ℝ) :
    dist (volterraIntegrand lower upper ordered coefficient source first radius)
      (volterraIntegrand lower upper ordered coefficient source second radius) ≤
    bound * dist (curveExtension lower upper ordered first radius)
      (curveExtension lower upper ordered second radius) := by
  unfold volterraIntegrand
  rw [dist_add_right, dist_eq_norm, dist_eq_norm, ← map_sub]
  exact ((coefficient (projIcc lower upper ordered radius)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (bounded _) (norm_nonneg _))

end Grad.AnnularLowVolterra
