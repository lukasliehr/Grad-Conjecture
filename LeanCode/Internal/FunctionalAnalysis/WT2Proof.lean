import WT2Interface

noncomputable section

open MeasureTheory Grad.PDEBootstrap Function
open scoped ContDiff

namespace Grad.WeakTesting.Separation

theorem coordinate_locallyIntegrable (dimension : ℕ) (domain : Set Spatial) (cell : ℤ)
    (coordinate : Fin dimension) (field : Fields dimension domain) :
    LocallyIntegrable (fun point => field point cell coordinate) (volume.restrict domain) :=
  ((coordinateMap dimension cell coordinate).comp_memLp field).locallyIntegrable
    (by norm_num : (1 : ENNReal) ≤ 2)

theorem coordinatePairing_apply (dimension : ℕ) (domain : Set Spatial) (cell : ℤ)
    (coordinate : Fin dimension) (test : Spatial → ℝ) (smoothness : ContDiff ℝ ∞ test)
    (compactSupport : HasCompactSupport test) (field : Fields dimension domain) :
    compactPairing dimension domain cell (EuclideanSpace.single coordinate (1 : ℂ))
        test smoothness compactSupport field =
      ∫ point in domain, test point • field point cell coordinate := by
  rw [compactPairing_apply]
  simp only [EuclideanSpace.inner_single_left, map_one, one_mul]

theorem coordinate_ae_eq_zero (dimension : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (cell : ℤ) (coordinate : Fin dimension) (field : Fields dimension domain)
    (vanishes : ∀ (test : Spatial → ℝ) (smoothness : ContDiff ℝ ∞ test)
      (compactSupport : HasCompactSupport test), tsupport test ⊆ domain →
        compactPairing dimension domain cell (EuclideanSpace.single coordinate (1 : ℂ))
          test smoothness compactSupport field = 0) :
    ∀ᵐ point ∂volume.restrict domain, field point cell coordinate = 0 := by
  have zeroOn : ∀ᵐ point ∂volume.restrict domain,
      point ∈ domain → field point cell coordinate = 0 := by
    apply openDomain.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((coordinate_locallyIntegrable dimension domain cell coordinate field).locallyIntegrableOn domain)
    intro test smoothness compactSupport supported
    rw [← coordinatePairing_apply dimension domain cell coordinate test smoothness compactSupport field]
    exact vanishes test smoothness compactSupport supported
  filter_upwards [zeroOn, ae_restrict_mem openDomain.measurableSet] with point zeroAt inside
  exact zeroAt inside

theorem separation : SeparationGoal := by
  intro dimension domain openDomain field vanishes
  have coordinates : ∀ (cell : ℤ) (coordinate : Fin dimension),
      ∀ᵐ point ∂volume.restrict domain, field point cell coordinate = 0 := by
    intro cell coordinate
    exact coordinate_ae_eq_zero dimension domain openDomain cell coordinate field
      (vanishes cell (EuclideanSpace.single coordinate (1 : ℂ)))
  have allCoordinates : ∀ᵐ point ∂volume.restrict domain,
      ∀ (cell : ℤ) (coordinate : Fin dimension), field point cell coordinate = 0 :=
    ae_all_iff.2 (fun cell => ae_all_iff.2 (coordinates cell))
  apply Lp.ext
  filter_upwards [allCoordinates, Lp.coeFn_zero (Cells dimension) 2 (volume.restrict domain)]
    with point zeroCoordinates zeroRepresentative
  rw [zeroRepresentative]
  apply lp.ext
  funext cell
  apply PiLp.ext
  intro coordinate
  exact zeroCoordinates cell coordinate

theorem equality : EqualityGoal := by
  intro dimension domain openDomain first second sameTests
  apply sub_eq_zero.mp
  apply separation dimension domain openDomain (first - second)
  intro cell vector test smoothness compactSupport supported
  calc
    compactPairing dimension domain cell vector test smoothness compactSupport (first - second) =
        compactPairing dimension domain cell vector test smoothness compactSupport first -
          compactPairing dimension domain cell vector test smoothness compactSupport second :=
      (compactPairing dimension domain cell vector test smoothness compactSupport).map_sub first second
    _ = 0 := sub_eq_zero.mpr (sameTests cell vector test smoothness compactSupport supported)

theorem compactPairing_toLp_apply (dimension : ℕ) (domain : Set Spatial) (cell : ℤ)
    (vector : Values dimension) (test : Spatial → ℝ) (smoothness : ContDiff ℝ ∞ test)
    (compactSupport : HasCompactSupport test) (field : Spatial → Cells dimension)
    (membership : MemLp field 2 (volume.restrict domain)) :
    compactPairing dimension domain cell vector test smoothness compactSupport
        (membership.toLp field) =
      ∫ point in domain, test point • inner ℂ vector (field point cell) := by
  rw [compactPairing_apply]
  apply integral_congr_ae
  filter_upwards [membership.coeFn_toLp] with point represented
  rw [represented]

theorem representatives : RepresentativeGoal := by
  intro dimension domain openDomain first second firstMembership secondMembership sameTests
  have fieldsEqual : firstMembership.toLp first = secondMembership.toLp second := by
    apply equality dimension domain openDomain
    intro cell vector test smoothness compactSupport supported
    simpa only [compactPairing_toLp_apply] using
      sameTests cell vector test smoothness compactSupport supported
  filter_upwards [firstMembership.coeFn_toLp, secondMembership.coeFn_toLp]
    with point firstRepresentative secondRepresentative
  exact firstRepresentative.symm.trans
    ((congrArg (fun field : Fields dimension domain => field point) fieldsEqual).trans
      secondRepresentative)

end Grad.WeakTesting.Separation
