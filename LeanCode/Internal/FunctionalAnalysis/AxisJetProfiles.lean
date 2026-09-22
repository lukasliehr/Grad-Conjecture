import AxisJetCarrier

noncomputable section

open scoped BigOperators ContDiff Topology

namespace Grad.AxisJet

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.AxisSplit

variable {parameters : PhaseParameters}

/-! ### M28: the fixed cap and the literal scaled profiles

`φ` is the lane's fixed radial cap at interface radius `1/2`: smooth, equal
to one on radius `1/8`, supported in the open ball of radius `1/4`. The
literal M28 profiles are `(E0 a)_n(y) = a_n φ(λ_n y)` and
`(E_i a)_n(y) = a_n y_i φ(λ_n y)` with `λ_n` the cell frequency. -/

/-- M28's fixed profile bump `φ`. -/
def jetBump : ContDiffBump (0 : SpatialPlane) := capBump (1 / 2) (by norm_num)

theorem jetBump_rIn : jetBump.rIn = 1 / 8 := by
  show (1 / 2 : ℝ) / 4 = 1 / 8
  norm_num

theorem jetBump_rOut : jetBump.rOut = 1 / 4 := by
  show (1 / 2 : ℝ) / 2 = 1 / 4
  norm_num

/-- M28's support inclusion: `supp φ ⊆ {|y| < 1/4}`. -/
theorem jetBump_support : Function.support ⇑jetBump =
    Metric.ball (0 : SpatialPlane) (1 / 4) := by
  rw [jetBump.support_eq, jetBump_rOut]

/-- M28's normalization `φ(0) = 1`. -/
theorem jetBump_origin : jetBump (0 : SpatialPlane) = 1 :=
  capBump_at_origin (1 / 2) (by norm_num)

/-- The literal scaled M28 value-profile scalar `y ↦ φ(λ_n y)`. -/
def profileScalarZero (cell : ℤ) : SpatialPlane → ℝ :=
  fun point => jetBump (cellFrequency cell • point)

/-- The literal scaled M28 coordinate-profile scalar `y ↦ y_i φ(λ_n y)`. -/
def profileScalarOne (coordinate : Fin 2) (cell : ℤ) : SpatialPlane → ℝ :=
  fun point => coordinateLinear coordinate point * jetBump (cellFrequency cell • point)

theorem profileScalarZero_smooth (cell : ℤ) : ContDiff ℝ ∞ (profileScalarZero cell) := by
  have scaleSmooth : ContDiff ℝ ∞ (fun point : SpatialPlane => cellFrequency cell • point) :=
    contDiff_id.const_smul (cellFrequency cell)
  exact jetBump.contDiff.comp scaleSmooth

theorem profileScalarOne_smooth (coordinate : Fin 2) (cell : ℤ) :
    ContDiff ℝ ∞ (profileScalarOne coordinate cell) :=
  ((coordinateLinear coordinate).contDiff).mul (profileScalarZero_smooth cell)

/-- The scaled value profile vanishes outside radius `1/(4 λ_n)`. -/
theorem profileScalarZero_vanish (cell : ℤ) (point : SpatialPlane)
    (outside : point ∉ Metric.closedBall (0 : SpatialPlane)
      ((4 * cellFrequency cell)⁻¹)) :
    profileScalarZero cell point = 0 := by
  have farPoint : (4 * cellFrequency cell)⁻¹ < ‖point‖ := by
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at outside
    exact outside
  have notSupport : cellFrequency cell • point ∉ Function.support ⇑jetBump := by
    rw [jetBump_support, Metric.mem_ball, dist_zero_right, not_lt, norm_smul,
      Real.norm_of_nonneg (cellFrequency_pos cell).le]
    have scaledFar : cellFrequency cell * (4 * cellFrequency cell)⁻¹ ≤
        cellFrequency cell * ‖point‖ :=
      mul_le_mul_of_nonneg_left farPoint.le (cellFrequency_pos cell).le
    have cancel : cellFrequency cell * (4 * cellFrequency cell)⁻¹ = 1 / 4 := by
      rw [mul_inv]
      rw [show cellFrequency cell * (4⁻¹ * (cellFrequency cell)⁻¹) =
        (cellFrequency cell * (cellFrequency cell)⁻¹) * 4⁻¹ from by ring,
        mul_inv_cancel₀ (cellFrequency_pos cell).ne', one_mul]
      norm_num
    linarith
  exact Function.notMem_support.mp notSupport

theorem profileScalarOne_vanish (coordinate : Fin 2) (cell : ℤ) (point : SpatialPlane)
    (outside : point ∉ Metric.closedBall (0 : SpatialPlane)
      ((4 * cellFrequency cell)⁻¹)) :
    profileScalarOne coordinate cell point = 0 := by
  unfold profileScalarOne
  have scalarZero := profileScalarZero_vanish cell point outside
  unfold profileScalarZero at scalarZero
  rw [scalarZero, mul_zero]

/-- The scaled coordinate profile is the `λ_n⁻¹`-scaled dilation of the
fixed profile `z ↦ z_i φ(z)`. -/
theorem profileScalarOne_scaled (coordinate : Fin 2) (cell : ℤ) (point : SpatialPlane) :
    profileScalarOne coordinate cell point =
      (cellFrequency cell)⁻¹ *
        (coordinateLinear coordinate (cellFrequency cell • point) *
          jetBump (cellFrequency cell • point)) := by
  have coordinateScale :
      coordinateLinear coordinate (cellFrequency cell • point) =
        cellFrequency cell * coordinateLinear coordinate point := by
    rw [(coordinateLinear coordinate).map_smul]
    rfl
  show coordinateLinear coordinate point * jetBump (cellFrequency cell • point) = _
  rw [coordinateScale,
    show (cellFrequency cell)⁻¹ * (cellFrequency cell *
        coordinateLinear coordinate point * jetBump (cellFrequency cell • point)) =
      ((cellFrequency cell)⁻¹ * cellFrequency cell) *
        (coordinateLinear coordinate point * jetBump (cellFrequency cell • point))
      from by ring,
    inv_mul_cancel₀ (cellFrequency_pos cell).ne', one_mul]

/-! ### The profile jets -/

def profileFieldZero {dimension : ℕ} (cell : ℤ)
    (vector : ComplexEuclidean dimension) : SpatialPlane → ComplexEuclidean dimension :=
  fun point => profileScalarZero cell point • vector

theorem profileFieldZero_smooth {dimension : ℕ} (cell : ℤ)
    (vector : ComplexEuclidean dimension) :
    ContDiff ℝ ∞ (profileFieldZero cell vector) :=
  (profileScalarZero_smooth cell).smul contDiff_const

def profileFieldOne {dimension : ℕ} (coordinate : Fin 2) (cell : ℤ)
    (vector : ComplexEuclidean dimension) : SpatialPlane → ComplexEuclidean dimension :=
  fun point => profileScalarOne coordinate cell point • vector

theorem profileFieldOne_smooth {dimension : ℕ} (coordinate : Fin 2) (cell : ℤ)
    (vector : ComplexEuclidean dimension) :
    ContDiff ℝ ∞ (profileFieldOne coordinate cell vector) :=
  (profileScalarOne_smooth coordinate cell).smul contDiff_const

/-- M28's `(E0 a)_n` profile jet at one cell for one inserted value. -/
def profileJetZero {dimension : ℕ} (cell : ℤ) (vector : ComplexEuclidean dimension) :
    ClosedJet dimension :=
  globalClosedJet (profileFieldZero cell vector) (profileFieldZero_smooth cell vector)

/-- M28's `(E_i a)_n` profile jet at one cell for one inserted value. -/
def profileJetOne {dimension : ℕ} (coordinate : Fin 2) (cell : ℤ)
    (vector : ComplexEuclidean dimension) : ClosedJet dimension :=
  globalClosedJet (profileFieldOne coordinate cell vector)
    (profileFieldOne_smooth coordinate cell vector)

/-! ### Linearity of the profiles in the inserted value -/

theorem profileJetZero_add {dimension : ℕ} (cell : ℤ)
    (first second : ComplexEuclidean dimension) :
    profileJetZero cell (first + second) =
      profileJetZero cell first + profileJetZero cell second := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [closedJet_value_add]
  change profileScalarZero cell point.val • (first + second) =
    profileScalarZero cell point.val • first + profileScalarZero cell point.val • second
  exact smul_add _ _ _

theorem profileJetZero_smul {dimension : ℕ} (cell : ℤ) (scalar : ℂ)
    (vector : ComplexEuclidean dimension) :
    profileJetZero cell (scalar • vector) = scalar • profileJetZero cell vector := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [closedJet_value_smul]
  change profileScalarZero cell point.val • (scalar • vector) =
    scalar • (profileScalarZero cell point.val • vector)
  exact smul_comm _ _ _

theorem profileJetOne_add {dimension : ℕ} (coordinate : Fin 2) (cell : ℤ)
    (first second : ComplexEuclidean dimension) :
    profileJetOne coordinate cell (first + second) =
      profileJetOne coordinate cell first + profileJetOne coordinate cell second := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [closedJet_value_add]
  change profileScalarOne coordinate cell point.val • (first + second) =
    profileScalarOne coordinate cell point.val • first +
      profileScalarOne coordinate cell point.val • second
  exact smul_add _ _ _

theorem profileJetOne_smul {dimension : ℕ} (coordinate : Fin 2) (cell : ℤ)
    (scalar : ℂ) (vector : ComplexEuclidean dimension) :
    profileJetOne coordinate cell (scalar • vector) =
      scalar • profileJetOne coordinate cell vector := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [closedJet_value_smul]
  change profileScalarOne coordinate cell point.val • (scalar • vector) =
    scalar • (profileScalarOne coordinate cell point.val • vector)
  exact smul_comm _ _ _

/-! ### The exact origin traces of the profiles -/

theorem profileScalarZero_origin (cell : ℤ) :
    profileScalarZero cell originPoint.val = 1 := by
  unfold profileScalarZero
  rw [originPoint_val, smul_zero]
  exact jetBump_origin

/-- The scaled value profile is one near the axis. -/
theorem profileScalarZero_eventually_one (cell : ℤ) :
    profileScalarZero cell =ᶠ[𝓝 (0 : SpatialPlane)] fun _ => (1 : ℝ) := by
  have radiusPositive : 0 < jetBump.rIn / cellFrequency cell :=
    div_pos jetBump.rIn_pos (cellFrequency_pos cell)
  filter_upwards [Metric.ball_mem_nhds (0 : SpatialPlane) radiusPositive]
    with point membership
  apply jetBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
    Real.norm_of_nonneg (cellFrequency_pos cell).le]
  rw [Metric.mem_ball, dist_zero_right] at membership
  have scaled : cellFrequency cell * ‖point‖ ≤
      cellFrequency cell * (jetBump.rIn / cellFrequency cell) :=
    mul_le_mul_of_nonneg_left membership.le (cellFrequency_pos cell).le
  rwa [mul_div_cancel₀ jetBump.rIn (cellFrequency_pos cell).ne'] at scaled

/-- M31 raw trace: the value profile has axis value exactly the inserted
vector. -/
theorem profileJetZero_originValue {dimension : ℕ} (cell : ℤ)
    (vector : ComplexEuclidean dimension) :
    originValue (profileJetZero cell vector) = vector := by
  unfold originValue profileJetZero
  rw [globalClosedJet_value]
  change profileScalarZero cell originPoint.val • vector = vector
  rw [profileScalarZero_origin, one_smul]

/-- M31 raw trace: the value profile has vanishing axis first derivative. -/
theorem profileJetZero_originPartial {dimension : ℕ} (cell : ℤ) (direction : Fin 2)
    (vector : ComplexEuclidean dimension) :
    originPartial direction (profileJetZero cell vector) = 0 := by
  rw [originPartial_eq_closedDerivative]
  unfold profileJetZero
  rw [globalClosedJet_derivative, ← spatialPartial_eq_ordered]
  change fderiv ℝ (profileFieldZero cell vector) originPoint.val
    (spatialBasis direction) = _
  have scalarDifferentiable : DifferentiableAt ℝ (profileScalarZero cell)
      originPoint.val :=
    ((profileScalarZero_smooth cell).differentiable (by simp)).differentiableAt
  have smulForm : profileFieldZero cell vector =
      fun point => profileScalarZero cell point • vector := rfl
  rw [smulForm, fderiv_smul_const scalarDifferentiable vector,
    ContinuousLinearMap.smulRight_apply]
  have scalarDerivative : fderiv ℝ (profileScalarZero cell) originPoint.val = 0 := by
    rw [originPoint_val, (profileScalarZero_eventually_one cell).fderiv_eq]
    simp
  rw [scalarDerivative, zero_apply, zero_smul]

theorem profileScalarOne_origin (coordinate : Fin 2) (cell : ℤ) :
    profileScalarOne coordinate cell originPoint.val = 0 := by
  unfold profileScalarOne
  rw [originPoint_val]
  have coordinateZero : coordinateLinear coordinate (0 : SpatialPlane) = 0 := rfl
  rw [coordinateZero, zero_mul]

/-- M31 raw trace: the coordinate profile has vanishing axis value. -/
theorem profileJetOne_originValue {dimension : ℕ} (coordinate : Fin 2) (cell : ℤ)
    (vector : ComplexEuclidean dimension) :
    originValue (profileJetOne coordinate cell vector) = 0 := by
  unfold originValue profileJetOne
  rw [globalClosedJet_value]
  change profileScalarOne coordinate cell originPoint.val • vector = 0
  rw [profileScalarOne_origin, zero_smul]

/-- M31 raw trace: the coordinate profile has axis first derivative exactly
the Kronecker insertion of the vector. -/
theorem profileJetOne_originPartial {dimension : ℕ} (direction coordinate : Fin 2)
    (cell : ℤ) (vector : ComplexEuclidean dimension) :
    originPartial direction (profileJetOne coordinate cell vector) =
      if direction = coordinate then vector else 0 := by
  rw [originPartial_eq_closedDerivative]
  unfold profileJetOne
  rw [globalClosedJet_derivative, ← spatialPartial_eq_ordered]
  change fderiv ℝ (profileFieldOne coordinate cell vector) originPoint.val
    (spatialBasis direction) = _
  have coordinateDifferentiable : DifferentiableAt ℝ
      (fun point : SpatialPlane => coordinateLinear coordinate point)
      originPoint.val :=
    (((coordinateLinear coordinate).contDiff (n := ∞)).differentiable
      (by simp)).differentiableAt
  have bumpDifferentiable : DifferentiableAt ℝ (profileScalarZero cell)
      originPoint.val :=
    ((profileScalarZero_smooth cell).differentiable (by simp)).differentiableAt
  have scalarDifferentiable : DifferentiableAt ℝ
      (fun point => coordinateLinear coordinate point * profileScalarZero cell point)
      originPoint.val := coordinateDifferentiable.mul bumpDifferentiable
  have smulForm : profileFieldOne coordinate cell vector =
      fun point =>
        (coordinateLinear coordinate point * profileScalarZero cell point) • vector := rfl
  rw [smulForm, fderiv_smul_const scalarDifferentiable vector,
    ContinuousLinearMap.smulRight_apply]
  have productDerivative : fderiv ℝ
      (fun point => coordinateLinear coordinate point * profileScalarZero cell point)
      originPoint.val (spatialBasis direction) = spatialBasis direction coordinate := by
    rw [fderiv_fun_mul coordinateDifferentiable bumpDifferentiable]
    rw [add_apply, smul_apply, smul_apply]
    have coordinateZero : coordinateLinear coordinate originPoint.val = 0 :=
      originPoint_coordinate coordinate
    rw [coordinateZero, profileScalarZero_origin, zero_smul, one_smul, zero_add,
      (coordinateLinear coordinate).fderiv]
    rfl
  rw [productDerivative]
  have basisComponent : spatialBasis direction coordinate =
      if direction = coordinate then (1 : ℝ) else 0 := by
    change Pi.single (M := fun _ : Fin 2 => ℝ) direction 1 coordinate = _
    by_cases equal : direction = coordinate
    · rw [if_pos equal, ← equal]
      exact Pi.single_eq_same direction 1
    · rw [if_neg equal]
      exact Pi.single_eq_of_ne (fun collide => equal collide.symm) 1
  rw [basisComponent]
  by_cases equal : direction = coordinate
  · rw [if_pos equal, if_pos equal, one_smul]
  · rw [if_neg equal, if_neg equal, zero_smul]

/-! ### The phased profile fields and their supports -/

/-- The phase-weighted value profile as one global field. -/
def phasedFieldZero {dimension : ℕ} (cell : ℤ) (vector : ComplexEuclidean dimension) :
    SpatialPlane → ComplexEuclidean dimension :=
  fun point =>
    (cartesianWeight parameters cell point * profileScalarZero cell point) • vector

theorem phasedFieldZero_smooth {dimension : ℕ} (cell : ℤ)
    (vector : ComplexEuclidean dimension) :
    ContDiff ℝ ∞ (phasedFieldZero (parameters := parameters) cell vector) :=
  ((cartesianWeight_contDiff parameters cell).mul
    (profileScalarZero_smooth cell)).smul contDiff_const

/-- The phase-weighted coordinate profile as one global field. -/
def phasedFieldOne {dimension : ℕ} (coordinate : Fin 2) (cell : ℤ)
    (vector : ComplexEuclidean dimension) :
    SpatialPlane → ComplexEuclidean dimension :=
  fun point =>
    (cartesianWeight parameters cell point *
      profileScalarOne coordinate cell point) • vector

theorem phasedFieldOne_smooth {dimension : ℕ} (coordinate : Fin 2) (cell : ℤ)
    (vector : ComplexEuclidean dimension) :
    ContDiff ℝ ∞ (phasedFieldOne (parameters := parameters) coordinate cell vector) :=
  ((cartesianWeight_contDiff parameters cell).mul
    (profileScalarOne_smooth coordinate cell)).smul contDiff_const

/-- The phase weighting of the value profile is the phased global field. -/
theorem phaseWeighted_profileZero {dimension : ℕ} (cell : ℤ)
    (vector : ComplexEuclidean dimension) :
    phaseWeightedJet parameters cell (profileJetZero cell vector) =
      globalClosedJet (phasedFieldZero (parameters := parameters) cell vector)
        (phasedFieldZero_smooth cell vector) := by
  symm
  apply globalClosedJet_eq_of_restriction
  intro point
  change (cartesianWeight parameters cell point.val *
      profileScalarZero cell point.val) • vector =
    cartesianWeight parameters cell point.val •
      (profileJetZero cell vector).value point
  rw [mul_smul]
  rfl

/-- The phase weighting of the coordinate profile is the phased global field. -/
theorem phaseWeighted_profileOne {dimension : ℕ} (coordinate : Fin 2) (cell : ℤ)
    (vector : ComplexEuclidean dimension) :
    phaseWeightedJet parameters cell (profileJetOne coordinate cell vector) =
      globalClosedJet (phasedFieldOne (parameters := parameters) coordinate cell vector)
        (phasedFieldOne_smooth coordinate cell vector) := by
  symm
  apply globalClosedJet_eq_of_restriction
  intro point
  change (cartesianWeight parameters cell point.val *
      profileScalarOne coordinate cell point.val) • vector =
    cartesianWeight parameters cell point.val •
      (profileJetOne coordinate cell vector).value point
  rw [mul_smul]
  rfl

/-- The phased value profile is supported in the closed ball of radius
`1/(4 λ_n)`. -/
theorem phasedFieldZero_tsupport {dimension : ℕ} (cell : ℤ)
    (vector : ComplexEuclidean dimension) :
    tsupport (phasedFieldZero (parameters := parameters) cell vector) ⊆
      Metric.closedBall (0 : SpatialPlane) ((4 * cellFrequency cell)⁻¹) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro point pointIn
  by_contra outside
  apply Function.mem_support.mp pointIn
  unfold phasedFieldZero
  rw [profileScalarZero_vanish cell point outside, mul_zero, zero_smul]

/-- The phased coordinate profile is supported in the closed ball of radius
`1/(4 λ_n)`. -/
theorem phasedFieldOne_tsupport {dimension : ℕ} (coordinate : Fin 2) (cell : ℤ)
    (vector : ComplexEuclidean dimension) :
    tsupport (phasedFieldOne (parameters := parameters) coordinate cell vector) ⊆
      Metric.closedBall (0 : SpatialPlane) ((4 * cellFrequency cell)⁻¹) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro point pointIn
  by_contra outside
  apply Function.mem_support.mp pointIn
  unfold phasedFieldOne
  rw [profileScalarOne_vanish coordinate cell point outside, mul_zero, zero_smul]

end Grad.AxisJet
