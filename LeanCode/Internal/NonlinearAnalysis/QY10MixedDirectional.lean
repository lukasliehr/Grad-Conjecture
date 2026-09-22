import QY9MixedCoreNorms

noncomputable section

open Filter
open scoped Topology ContDiff

namespace Grad.Q24Realization

open Grad.CartesianState Grad.NonlinearQuotientBounds Grad.QuotientProjection

/-- Convert the original all-grade rows difference quotient into the
ordinary Banach derivative for any real core, including mixed finite seed
and complex field directions. This is a conversion lemma, not a presumed
derivative law for the nonlinear map. -/
theorem rows_hasDerivAt_of_directional {C : Type*} [AddCommGroup C] [Module ℝ C]
    (parameters : PhaseParameters) (grade : ℕ) (mapping : C → QuotientRows parameters)
    (base direction : C) (derivative : QuotientRows parameters)
    (genuine : ∀ q, Tendsto (fun t : ℝ => rowsGradeNorm q
      (t⁻¹ • (mapping (base + t • direction) - mapping base) - derivative))
      (𝓝[≠] (0 : ℝ)) (𝓝 0)) :
    HasDerivAt (fun t : ℝ => quotientEta parameters grade (mapping (base + t • direction)))
      (quotientEta parameters grade derivative) 0 := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have limit := (genuine grade).const_mul 2
  simp only [mul_zero] at limit
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ limit
  filter_upwards with t
  have bound := quotientEta_norm_le_rows parameters grade
    (t⁻¹ • (mapping (base + t • direction) - mapping base) - derivative)
  change ‖((quotientEta parameters grade).restrictScalars ℝ)
    (t⁻¹ • (mapping (base + t • direction) - mapping base) - derivative)‖ ≤ _ at bound
  rw [map_sub, map_smul, map_sub] at bound
  rw [slope_def_module, sub_zero, zero_smul ℝ direction, add_zero]
  exact bound

/-- Apply the genuine directional-tower identification at the literal
mixed core embedding. Its two analytic premises are discharged by the
owning mixed Q23 core block, not manufactured here. -/
theorem mixed_iteratedFDeriv_of_directional
    (parameters : PhaseParameters) (cellLength : ℝ) (reference : Grad.Constraints.Seed.Parameters)
    (grade : ℕ)
    (tower : (order : ℕ) → (Grad.Constraints.Seed.Parameters × JointState parameters) →
      (Fin order → Grad.Constraints.Seed.Parameters × JointState parameters) → QuotientRows parameters)
    (zeroth : ∀ base, mixedCoreEmbed parameters (grade + 6) base ∈ mixedDomain parameters (grade + 6) →
      ∀ directions, quotientEta parameters grade (tower 0 base directions) =
        completedMixedSlice parameters cellLength reference grade (mixedCoreEmbed parameters (grade + 6) base))
    (step : ∀ order base (directions : Fin (order + 1) → Grad.Constraints.Seed.Parameters × JointState parameters),
      mixedCoreEmbed parameters (grade + 6) base ∈ mixedDomain parameters (grade + 6) →
      ∀ q, Tendsto (fun t : ℝ => rowsGradeNorm q
        (t⁻¹ • (tower order (base + t • directions (Fin.last order))
          (fun position => directions position.castSucc) -
          tower order base (fun position => directions position.castSucc)) -
          tower (order + 1) base directions)) (𝓝[≠] (0 : ℝ)) (𝓝 0))
    (order : ℕ) (base : Grad.Constraints.Seed.Parameters × JointState parameters)
    (inside : mixedCoreEmbed parameters (grade + 6) base ∈ mixedDomain parameters (grade + 6))
    (directions : Fin order → Grad.Constraints.Seed.Parameters × JointState parameters) :
    iteratedFDeriv ℝ order (completedMixedSlice parameters cellLength reference grade)
      (mixedCoreEmbed parameters (grade + 6) base)
      (fun position => mixedCoreEmbed parameters (grade + 6) (directions position)) =
      quotientEta parameters grade (tower order base (fun position => directions position.rev)) := by
  apply iteratedFDeriv_core_of_directional (mixedCoreLinear parameters (grade + 6))
    (completedMixedSlice parameters cellLength reference grade) (mixedDomain parameters (grade + 6))
    (mixedDomain_isOpen parameters (grade + 6))
    (completedMixedSlice_contDiffOn parameters cellLength reference grade)
    (fun order base directions => quotientEta parameters grade (tower order base directions)) zeroth
  · intro count point tuple member
    exact rows_hasDerivAt_of_directional parameters grade
      (fun state => tower count state (fun position => tuple position.castSucc)) point (tuple (Fin.last count))
      (tower (count + 1) point tuple) (step count point tuple member)
  · exact inside

end Grad.Q24Realization
