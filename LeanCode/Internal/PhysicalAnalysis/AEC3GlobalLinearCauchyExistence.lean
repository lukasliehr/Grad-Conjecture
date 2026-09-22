import AEC2GlobalFactorialIteration

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat
namespace Grad.AnnularLowVolterra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem volterra_exists_fixed_point (lower upper : ℝ) (ordered : lower ≤ upper)
    (coefficient : C(Icc lower upper, E →L[ℝ] E)) (source : C(Icc lower upper, E))
    (initial : E) (bound : ℝ≥0) (bounded : ∀ point, ‖coefficient point‖ ≤ bound) :
    ∃ curve : C(Icc lower upper, E),
      IsFixedPt (volterraNext lower upper ordered coefficient source initial) curve := by
  obtain ⟨count, constant, contracting⟩ :=
    volterra_exists_contracting_iterate lower upper ordered coefficient source initial bound bounded
  exact ⟨_, contracting.isFixedPt_fixedPoint_iterate⟩

theorem volterra_fixed_point_unique (lower upper : ℝ) (ordered : lower ≤ upper)
    (coefficient : C(Icc lower upper, E →L[ℝ] E)) (source : C(Icc lower upper, E))
    (initial : E) (bound : ℝ≥0) (bounded : ∀ point, ‖coefficient point‖ ≤ bound)
    (first second : C(Icc lower upper, E))
    (firstFixed : IsFixedPt (volterraNext lower upper ordered coefficient source initial) first)
    (secondFixed : IsFixedPt (volterraNext lower upper ordered coefficient source initial) second) :
    first = second := by
  obtain ⟨count, constant, contracting⟩ :=
    volterra_exists_contracting_iterate lower upper ordered coefficient source initial bound bounded
  exact contracting.fixedPoint_unique' (firstFixed.iterate count) (secondFixed.iterate count)

def volterraPrimitive (lower upper : ℝ) (ordered : lower ≤ upper)
    (coefficient : C(Icc lower upper, E →L[ℝ] E)) (source : C(Icc lower upper, E))
    (initial : E) (curve : C(Icc lower upper, E)) (radius : ℝ) : E :=
  initial + ∫ point in lower..radius, volterraIntegrand lower upper ordered coefficient source curve point

theorem volterraPrimitive_hasDerivAt (lower upper : ℝ) (ordered : lower ≤ upper)
    (coefficient : C(Icc lower upper, E →L[ℝ] E)) (source : C(Icc lower upper, E))
    (initial : E) (curve : C(Icc lower upper, E)) (radius : ℝ) :
    HasDerivAt (volterraPrimitive lower upper ordered coefficient source initial curve)
      (volterraIntegrand lower upper ordered coefficient source curve radius) radius := by
  have continuous := volterraIntegrand_continuous lower upper ordered coefficient source curve
  exact (intervalIntegral.integral_hasDerivAt_right (continuous.intervalIntegrable _ _)
    continuous.aestronglyMeasurable.stronglyMeasurableAtFilter continuous.continuousAt).const_add initial

/-- Global linear Cauchy existence on an arbitrary compact real interval.
The derivative exists even at the endpoints for the displayed extension.
There is no smallness restriction on interval length or coefficient norm. -/
theorem globalLinearCauchy_exists (lower upper : ℝ) (ordered : lower ≤ upper)
    (coefficient : C(Icc lower upper, E →L[ℝ] E)) (source : C(Icc lower upper, E))
    (initial : E) (bound : ℝ≥0) (bounded : ∀ point, ‖coefficient point‖ ≤ bound) :
    ∃ solution : ℝ → E, solution lower = initial ∧
      ∀ point : Icc lower upper,
        HasDerivAt solution (coefficient point (solution point.val) + source point) point.val := by
  obtain ⟨curve, fixed⟩ := volterra_exists_fixed_point lower upper ordered coefficient source initial bound bounded
  refine ⟨volterraPrimitive lower upper ordered coefficient source initial curve, ?_, ?_⟩
  · simp only [volterraPrimitive, integral_same, add_zero]
  · intro point
    have value : volterraPrimitive lower upper ordered coefficient source initial curve point.val = curve point :=
      congrArg (fun field : C(Icc lower upper, E) => field point) fixed
    have derivative := volterraPrimitive_hasDerivAt lower upper ordered coefficient source initial curve point.val
    unfold volterraIntegrand at derivative
    rw [curveExtension_of_mem lower upper ordered curve point.val point.property,
      curveExtension_of_mem lower upper ordered source point.val point.property, projIcc_val,
      ← value] at derivative
    exact derivative

end Grad.AnnularLowVolterra
