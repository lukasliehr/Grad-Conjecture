import SampledGlobalEmbedding

noncomputable section

namespace Grad.PhysicalFamily.SampledGlobalEmbedding

theorem abs_arctan_le (value : ℝ) : |Real.arctan value| ≤ |value| := by
  have estimate := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := Real.arctan) (s := Set.univ) (C := 1)
    (fun point _ => Real.differentiableAt_arctan point)
    (fun point _ => show ‖deriv Real.arctan point‖ ≤ 1 by
      rw [Real.deriv_arctan, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ 1 / (1 + point ^ 2))]
      exact (div_le_one (by positivity)).2 (by nlinarith [sq_nonneg point]))
    convex_univ (Set.mem_univ (0 : ℝ)) (Set.mem_univ value)
  simpa using estimate

/-- Exact angular derivative, with the large radius kept in the denominator. -/
theorem cylindricalAngle_hasFDerivAt
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    (radial tangential : Space → ℝ) (point : Space)
    (radialDerivative tangentialDerivative : Space →L[ℝ] ℝ)
    (radialHasDerivative : HasFDerivAt radial radialDerivative point)
    (tangentialHasDerivative : HasFDerivAt tangential tangentialDerivative point)
    (radialPositive : 0 < radial point) (period : ℝ) :
    HasFDerivAt (fun argument => period *
      Real.arctan (tangential argument / radial argument))
      ((period / (radial point ^ 2 + tangential point ^ 2)) •
        (radial point • tangentialDerivative -
          tangential point • radialDerivative)) point := by
  have inverseDerivative := (hasDerivAt_inv radialPositive.ne').comp_hasFDerivAt
    point radialHasDerivative
  have derivative :=
    ((tangentialHasDerivative.mul inverseDerivative).arctan).const_mul period
  have derivative' : HasFDerivAt (fun argument => period *
      Real.arctan (tangential argument / radial argument))
      (period • (1 / (1 + (tangential point / radial point) ^ 2)) •
        (tangential point • (-(radial point ^ 2)⁻¹) • radialDerivative +
          (radial point)⁻¹ • tangentialDerivative)) point := by
    simpa only [Pi.mul_apply, Function.comp_apply, div_eq_mul_inv] using derivative
  apply derivative'.congr_fderiv
  ext direction
  simp only [smul_apply, sub_apply, add_apply, smul_eq_mul]
  have denominatorPositive : 0 < radial point ^ 2 + tangential point ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos radialPositive) (sq_nonneg _)
  field_simp [radialPositive.ne', denominatorPositive.ne']
  ring

/-- The quantitative G08 angular estimate.  Both the value and the Euclidean
operator derivative lose precisely one large-radius factor, canceled by N. -/
theorem cylindricalAngle_value_fderiv_bound
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    (radial tangential : Space → ℝ) (point : Space)
    (radialDerivative tangentialDerivative : Space →L[ℝ] ℝ)
    (radialHasDerivative : HasFDerivAt radial radialDerivative point)
    (tangentialHasDerivative : HasFDerivAt tangential tangentialDerivative point)
    (period cellLength error derivativeBound : ℝ)
    (periodPositive : 0 < period) (cellLengthPositive : 0 < cellLength)
    (radiusLarge : 1 ≤ period * cellLength)
    (radialLower : period * cellLength / 2 ≤ radial point)
    (errorNonnegative : 0 ≤ error)
    (tangentialValueBound : |tangential point| ≤ error)
    (tangentialDerivativeBound : ‖tangentialDerivative‖ ≤ error)
    (radialDerivativeBound : ‖radialDerivative‖ ≤ derivativeBound) :
    |period * Real.arctan (tangential point / radial point)| ≤
        ((2 + 4 * derivativeBound) / cellLength) * error ∧
      ‖fderiv ℝ (fun argument => period *
        Real.arctan (tangential argument / radial argument)) point‖ ≤
        ((2 + 4 * derivativeBound) / cellLength) * error := by
  let radius := period * cellLength
  let denominator := radial point ^ 2 + tangential point ^ 2
  have radiusPositive : 0 < radius := mul_pos periodPositive cellLengthPositive
  have radialPositive : 0 < radial point := lt_of_lt_of_le
    (half_pos radiusPositive) radialLower
  have denominatorPositive : 0 < denominator :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos radialPositive) (sq_nonneg _)
  have derivativeBoundNonnegative : 0 ≤ derivativeBound :=
    (norm_nonneg _).trans radialDerivativeBound
  have inverseRadialBound : 1 / radial point ≤ 2 / radius := by
    apply (div_le_div_iff₀ radialPositive radiusPositive).2
    dsimp [radius]
    linarith
  have firstFraction : radial point / denominator ≤ 2 / radius := by
    apply (div_le_div_iff₀ denominatorPositive radiusPositive).2
    have lower : radius ≤ 2 * radial point := by linarith
    have multiplied := mul_le_mul_of_nonneg_right lower radialPositive.le
    dsimp [denominator]
    nlinarith [sq_nonneg (tangential point)]
  have secondFraction : 1 / denominator ≤ 4 / radius := by
    apply (div_le_div_iff₀ denominatorPositive radiusPositive).2
    have radiusAtLeastOne : 1 ≤ radius := radiusLarge
    have lower : radius ≤ 2 * radial point := by linarith
    have lowerSquare := pow_le_pow_left₀ radiusPositive.le lower 2
    dsimp [denominator]
    nlinarith [sq_nonneg (tangential point)]
  have constantIdentity :
      period * error * (2 / radius + derivativeBound * (4 / radius)) =
        ((2 + 4 * derivativeBound) / cellLength) * error := by
    dsimp [radius]
    field_simp
  constructor
  · calc
      |period * Real.arctan (tangential point / radial point)| =
          period * |Real.arctan (tangential point / radial point)| := by
        rw [abs_mul, abs_of_pos periodPositive]
      _ ≤ period * |tangential point / radial point| :=
        mul_le_mul_of_nonneg_left (abs_arctan_le _) periodPositive.le
      _ ≤ period * (error / radial point) := by
        rw [abs_div, abs_of_pos radialPositive]
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right tangentialValueBound radialPositive.le)
          periodPositive.le
      _ ≤ period * error * (2 / radius) := by
        simpa only [div_eq_mul_inv, one_mul, mul_assoc] using
          mul_le_mul_of_nonneg_left inverseRadialBound
            (mul_nonneg periodPositive.le errorNonnegative)
      _ ≤ period * error * (2 / radius + derivativeBound * (4 / radius)) := by
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity))
          (mul_nonneg periodPositive.le errorNonnegative)
      _ = _ := constantIdentity
  · rw [(cylindricalAngle_hasFDerivAt radial tangential point radialDerivative
      tangentialDerivative radialHasDerivative tangentialHasDerivative
      radialPositive period).fderiv]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg periodPositive.le denominatorPositive.le)]
    calc
      period / denominator *
          ‖radial point • tangentialDerivative -
            tangential point • radialDerivative‖ ≤
        period / denominator *
          (radial point * ‖tangentialDerivative‖ +
            |tangential point| * ‖radialDerivative‖) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos radialPositive] using
          norm_sub_le (radial point • tangentialDerivative)
            (tangential point • radialDerivative)
      _ ≤ period / denominator * (radial point * error + error * derivativeBound) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left tangentialDerivativeBound
            radialPositive.le)
            (mul_le_mul tangentialValueBound radialDerivativeBound
              (norm_nonneg _) errorNonnegative)) (by positivity)
      _ = period * error *
          (radial point / denominator + derivativeBound * (1 / denominator)) := by
        ring
      _ ≤ period * error * (2 / radius + derivativeBound * (4 / radius)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add firstFraction
            (mul_le_mul_of_nonneg_left secondFraction derivativeBoundNonnegative))
          (mul_nonneg periodPositive.le errorNonnegative)
      _ = _ := constantIdentity

/-- Exact differential of the small radial correction. -/
theorem cylindricalRadialCorrection_hasFDerivAt
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    (radial tangential : Space → ℝ) (point : Space)
    (radialDerivative tangentialDerivative : Space →L[ℝ] ℝ)
    (radialHasDerivative : HasFDerivAt radial radialDerivative point)
    (tangentialHasDerivative : HasFDerivAt tangential tangentialDerivative point)
    (radialPositive : 0 < radial point) :
    let radius := Real.sqrt (radial point ^ 2 + tangential point ^ 2)
    HasFDerivAt (fun argument =>
      Real.sqrt (radial argument ^ 2 + tangential argument ^ 2) - radial argument)
      ((-(radius - radial point) / radius) • radialDerivative +
        (tangential point / radius) • tangentialDerivative) point := by
  dsimp only
  have squaredPositive : 0 < radial point ^ 2 + tangential point ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos radialPositive) (sq_nonneg _)
  have radiusPositive := Real.sqrt_pos.2 squaredPositive
  have derivative := (((radialHasDerivative.pow 2).add
    (tangentialHasDerivative.pow 2)).sqrt squaredPositive.ne').sub radialHasDerivative
  apply derivative.congr_fderiv
  ext direction
  simp only [smul_apply, sub_apply, add_apply, smul_eq_mul]
  norm_num
  field_simp
  ring

/-- Rationalization and the exact radial differential give the G08 radial
correction estimate with a constant independent of the major radius. -/
theorem cylindricalRadialCorrection_value_fderiv_bound
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    (radial tangential : Space → ℝ) (point : Space)
    (radialDerivative tangentialDerivative : Space →L[ℝ] ℝ)
    (radialHasDerivative : HasFDerivAt radial radialDerivative point)
    (tangentialHasDerivative : HasFDerivAt tangential tangentialDerivative point)
    (majorRadius error derivativeBound : ℝ)
    (radiusLarge : 1 ≤ majorRadius)
    (radialLower : majorRadius / 2 ≤ radial point)
    (errorNonnegative : 0 ≤ error) (errorSmall : error ≤ 1)
    (tangentialValueBound : |tangential point| ≤ error)
    (tangentialDerivativeBound : ‖tangentialDerivative‖ ≤ error)
    (radialDerivativeBound : ‖radialDerivative‖ ≤ derivativeBound) :
    let radius := Real.sqrt (radial point ^ 2 + tangential point ^ 2)
    0 ≤ radius - radial point ∧
      radius - radial point ≤ error ^ 2 / majorRadius ∧
      |radius - radial point| ≤ (2 * derivativeBound + 2) * error ∧
      ‖fderiv ℝ (fun argument =>
        Real.sqrt (radial argument ^ 2 + tangential argument ^ 2) -
          radial argument) point‖ ≤ (2 * derivativeBound + 2) * error := by
  let radius := Real.sqrt (radial point ^ 2 + tangential point ^ 2)
  have majorRadiusPositive : 0 < majorRadius := lt_of_lt_of_le zero_lt_one radiusLarge
  have radialPositive : 0 < radial point :=
    lt_of_lt_of_le (half_pos majorRadiusPositive) radialLower
  have squaredPositive : 0 < radial point ^ 2 + tangential point ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos radialPositive) (sq_nonneg _)
  have radiusPositive : 0 < radius := Real.sqrt_pos.2 squaredPositive
  have radiusSquare : radius ^ 2 = radial point ^ 2 + tangential point ^ 2 :=
    Real.sq_sqrt squaredPositive.le
  have radialLeRadius : radial point ≤ radius := by
    apply (sq_le_sq₀ radialPositive.le radiusPositive.le).mp
    rw [radiusSquare]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have errorPositive : 0 ≤ radius - radial point := sub_nonneg.2 radialLeRadius
  have tangentialSquare : tangential point ^ 2 ≤ error ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) errorNonnegative).mpr tangentialValueBound
  have errorRationalized : radius - radial point ≤ error ^ 2 / majorRadius := by
    apply (le_div_iff₀ majorRadiusPositive).2
    have denominatorLower : majorRadius ≤ radius + radial point := by linarith
    have multiplied := mul_le_mul_of_nonneg_left denominatorLower errorPositive
    nlinarith
  have inverseRadius : 1 / radius ≤ 2 := by
    apply (div_le_iff₀ radiusPositive).2
    linarith
  have errorCoarse : radius - radial point ≤ error := by
    have squareSmall : error ^ 2 ≤ error := by nlinarith
    have divisionSmall : error ^ 2 / majorRadius ≤ error ^ 2 :=
      div_le_self (sq_nonneg _) radiusLarge
    exact errorRationalized.trans (divisionSmall.trans squareSmall)
  have derivativeBoundNonnegative : 0 ≤ derivativeBound :=
    (norm_nonneg _).trans radialDerivativeBound
  refine ⟨errorPositive, errorRationalized, ?_, ?_⟩
  · rw [abs_of_nonneg errorPositive]
    exact errorCoarse.trans (by nlinarith)
  · rw [(cylindricalRadialCorrection_hasFDerivAt radial tangential point
      radialDerivative tangentialDerivative radialHasDerivative
      tangentialHasDerivative radialPositive).fderiv]
    calc
      ‖(-(radius - radial point) / radius) • radialDerivative +
          (tangential point / radius) • tangentialDerivative‖ ≤
        (radius - radial point) / radius * ‖radialDerivative‖ +
          |tangential point| / radius * ‖tangentialDerivative‖ := by
        simpa only [norm_smul, Real.norm_eq_abs, abs_div, abs_neg,
          abs_of_nonneg errorPositive, abs_of_pos radiusPositive] using
          norm_add_le ((-(radius - radial point) / radius) • radialDerivative)
            ((tangential point / radius) • tangentialDerivative)
      _ ≤ (error * 2) * derivativeBound + (error * 2) * error := by
        apply add_le_add
        · apply mul_le_mul _ radialDerivativeBound (norm_nonneg _)
            (mul_nonneg errorNonnegative (by norm_num))
          simpa only [div_eq_mul_inv, one_mul] using
            mul_le_mul errorCoarse inverseRadius (by positivity) errorNonnegative
        · apply mul_le_mul _ tangentialDerivativeBound (norm_nonneg _)
            (mul_nonneg errorNonnegative (by norm_num))
          simpa only [div_eq_mul_inv, one_mul] using
            mul_le_mul tangentialValueBound inverseRadius (by positivity) errorNonnegative
      _ ≤ (2 * derivativeBound + 2) * error := by nlinarith

end Grad.PhysicalFamily.SampledGlobalEmbedding
