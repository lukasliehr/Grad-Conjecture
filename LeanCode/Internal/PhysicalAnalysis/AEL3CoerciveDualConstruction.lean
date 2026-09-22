import AEL2ActualComplexWeakCorrespondence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.AnnularCurrentInverse

/-- Internal Riesz/Lax-Milgram construction used below with the proved actual
current coercivity. Its forward equation is exactly the supplied bilinear form. -/
def coerciveDualEquiv {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (form : V →L[ℝ] V →L[ℝ] ℝ) (coercive : IsCoercive form) :
    (V →L[ℝ] ℝ) ≃L[ℝ] V :=
  (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.trans
    coercive.continuousLinearEquivOfBilin.symm

theorem coerciveDualEquiv_solves {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (form : V →L[ℝ] V →L[ℝ] ℝ) (coercive : IsCoercive form)
    (source : V →L[ℝ] ℝ) (test : V) :
    form (coerciveDualEquiv form coercive source) test = source test := by
  have equality := coercive.continuousLinearEquivOfBilin_apply
    (coercive.continuousLinearEquivOfBilin.symm ((InnerProductSpace.toDual ℝ V).symm source)) test
  rw [ContinuousLinearEquiv.apply_symm_apply, InnerProductSpace.toDual_symm_apply] at equality
  exact equality.symm

theorem coerciveDualEquiv_forward {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (form : V →L[ℝ] V →L[ℝ] ℝ) (coercive : IsCoercive form) :
    form.comp (coerciveDualEquiv form coercive).toContinuousLinearMap = ContinuousLinearMap.id ℝ (V →L[ℝ] ℝ) := by
  ext source test
  exact coerciveDualEquiv_solves form coercive source test

theorem coerciveDualEquiv_inverse {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (form : V →L[ℝ] V →L[ℝ] ℝ) (coercive : IsCoercive form) :
    (coerciveDualEquiv form coercive).toContinuousLinearMap.comp form = ContinuousLinearMap.id ℝ V := by
  ext field
  apply (coerciveDualEquiv form coercive).symm.injective
  have equation : form field = (coerciveDualEquiv form coercive).symm field := by
    have law := coerciveDualEquiv_forward form coercive
    have point := congrArg (fun mapping => mapping ((coerciveDualEquiv form coercive).symm field)) law
    simpa using point
  change (coerciveDualEquiv form coercive).symm (coerciveDualEquiv form coercive (form field)) =
    (coerciveDualEquiv form coercive).symm field
  rw [ContinuousLinearEquiv.symm_apply_apply, equation]

theorem coerciveDualEquiv_bound {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (form : V →L[ℝ] V →L[ℝ] ℝ) (coercive : IsCoercive form)
    (bound : ∀ field, (1 / 32 : ℝ) * ‖field‖ ^ 2 ≤ form field field)
    (source : V →L[ℝ] ℝ) : ‖coerciveDualEquiv form coercive source‖ ≤ 32 * ‖source‖ := by
  let solution := coerciveDualEquiv form coercive source
  have positiveForm := bound solution
  rw [coerciveDualEquiv_solves] at positiveForm
  have estimate := (le_abs_self (source solution)).trans (source.le_opNorm solution)
  by_cases zero : ‖solution‖ = 0
  · change ‖solution‖ ≤ _
    rw [zero]
    positivity
  · have positiveNorm : 0 < ‖solution‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm zero)
    change ‖solution‖ ≤ _
    nlinarith only [positiveForm, estimate, positiveNorm]

end Grad.AnnularCurrentInverse
