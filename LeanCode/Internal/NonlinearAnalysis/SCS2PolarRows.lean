import SCS1DivisionCompatibility

noncomputable section
open scoped BigOperators

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarAngular Grad.Constraints.Gauges

def rowAsGraph {dimension : ℕ} (lower : ℝ) (positive : 0 < lower)
    (row : DivisionRow dimension lower) : annularDerivativeGraph dimension lower positive 0 :=
  ⟨WithLp.toLp 1 (fun _ : Fin 1 => row),
    (annularDerivativeGraph_mem_iff lower positive 0 _).mpr (fun index => Fin.elim0 index)⟩

theorem zeroGraph_norm {dimension : ℕ} (lower : ℝ) (positive : 0 < lower)
    (field : annularDerivativeGraph dimension lower positive 0) : ‖field‖ = ‖field.val 0‖ := by
  change ‖field.val‖ = _
  rw [PiLp.norm_eq_of_L1, Fin.sum_univ_one]

theorem rowAsGraph_norm {dimension : ℕ} (lower : ℝ) (positive : 0 < lower)
    (row : DivisionRow dimension lower) : ‖rowAsGraph lower positive row‖ = ‖row‖ :=
  zeroGraph_norm lower positive _

def radialRowContraction (lower : ℝ) (positive : 0 < lower) (power : ℕ)
    (row : DivisionRow 2 lower) : DivisionRow 1 lower :=
  (annularRadialContraction lower positive power (rowAsGraph lower positive row)).val 0

def tangentialRowContraction (lower : ℝ) (positive : 0 < lower) (power : ℕ)
    (row : DivisionRow 2 lower) : DivisionRow 1 lower :=
  (annularTangentialContraction lower positive power (rowAsGraph lower positive row)).val 0

theorem radialRowContraction_bound (lower : ℝ) (positive : 0 < lower) (power : ℕ)
    (row : DivisionRow 2 lower) :
    ‖radialRowContraction lower positive power row‖ ≤ 2 * 2 ^ power * ‖row‖ := by
  rw [radialRowContraction, ← zeroGraph_norm]
  exact (annularRadialContraction_apply_norm_le lower positive power _).trans_eq
    (by rw [rowAsGraph_norm])

theorem tangentialRowContraction_bound (lower : ℝ) (positive : 0 < lower) (power : ℕ)
    (row : DivisionRow 2 lower) :
    ‖tangentialRowContraction lower positive power row‖ ≤ 2 * 2 ^ power * ‖row‖ := by
  rw [tangentialRowContraction, ← zeroGraph_norm]
  exact (annularTangentialContraction_apply_norm_le lower positive power _).trans_eq
    (by rw [rowAsGraph_norm])

theorem _root_.Grad.SourceCollarCoefficients.RadialRowsCompatible.add {dimension power : ℕ} {lower : ℝ}
    {a b c d : DivisionRow dimension lower}
    (first : RadialRowsCompatible lower power a b) (second : RadialRowsCompatible lower power c d) :
    RadialRowsCompatible lower power (a + c) (b + d) := by
  intro mode
  change a mode + c mode = _ • (b mode + d mode)
  rw [first, second, smul_add]

theorem _root_.Grad.SourceCollarCoefficients.RadialRowsCompatible.sub {dimension power : ℕ} {lower : ℝ}
    {a b c d : DivisionRow dimension lower}
    (first : RadialRowsCompatible lower power a b) (second : RadialRowsCompatible lower power c d) :
    RadialRowsCompatible lower power (a - c) (b - d) := by
  intro mode
  change a mode - c mode = _ • (b mode - d mode)
  rw [first, second, smul_sub]

theorem _root_.Grad.SourceCollarCoefficients.RadialRowsCompatible.smul {dimension power : ℕ} {lower : ℝ}
    {high low : DivisionRow dimension lower} (compatible : RadialRowsCompatible lower power high low)
    (scalar : ℂ) : RadialRowsCompatible lower power (scalar • high) (scalar • low) := by
  intro mode
  change scalar • high mode = _ • (scalar • low mode)
  rw [compatible, smul_comm]

def cosineRow {dimension : ℕ} (lower : ℝ) (power : ℕ) (row : DivisionRow dimension lower) :=
  (2 : ℂ)⁻¹ • (annularRowShift lower power 1 row + annularRowShift lower power (-1) row)

def sineRow {dimension : ℕ} (lower : ℝ) (power : ℕ) (row : DivisionRow dimension lower) :=
  (2 * Complex.I : ℂ)⁻¹ • (annularRowShift lower power 1 row - annularRowShift lower power (-1) row)

theorem radialRowContraction_formula (lower : ℝ) (positive : 0 < lower) (power : ℕ)
    (row : DivisionRow 2 lower) :
    radialRowContraction lower positive power row =
      divisionRowValueMap lower (planarComponentMap 0) (cosineRow lower power row) +
      divisionRowValueMap lower (planarComponentMap 1) (sineRow lower power row) := rfl

theorem tangentialRowContraction_formula (lower : ℝ) (positive : 0 < lower) (power : ℕ)
    (row : DivisionRow 2 lower) :
    tangentialRowContraction lower positive power row =
      divisionRowValueMap lower (planarComponentMap 1) (cosineRow lower power row) -
      divisionRowValueMap lower (planarComponentMap 0) (sineRow lower power row) := rfl

theorem _root_.Grad.SourceCollarCoefficients.RadialRowsCompatible.cosine {dimension power : ℕ} {lower : ℝ}
    {high low : DivisionRow dimension lower} (compatible : RadialRowsCompatible lower power high low) :
    RadialRowsCompatible lower power (cosineRow lower power high) (cosineRow lower 0 low) :=
  ((compatible.shift 1).add (compatible.shift (-1))).smul _

theorem _root_.Grad.SourceCollarCoefficients.RadialRowsCompatible.sine {dimension power : ℕ} {lower : ℝ}
    {high low : DivisionRow dimension lower} (compatible : RadialRowsCompatible lower power high low) :
    RadialRowsCompatible lower power (sineRow lower power high) (sineRow lower 0 low) :=
  ((compatible.shift 1).sub (compatible.shift (-1))).smul _

theorem _root_.Grad.SourceCollarCoefficients.RadialRowsCompatible.radial {power : ℕ} {lower : ℝ} (positive : 0 < lower)
    {high low : DivisionRow 2 lower} (compatible : RadialRowsCompatible lower power high low) :
    RadialRowsCompatible lower power (radialRowContraction lower positive power high)
      (radialRowContraction lower positive 0 low) := by
  rw [radialRowContraction_formula, radialRowContraction_formula]
  exact (compatible.cosine.valueMap _).add (compatible.sine.valueMap _)

theorem _root_.Grad.SourceCollarCoefficients.RadialRowsCompatible.tangential {power : ℕ} {lower : ℝ} (positive : 0 < lower)
    {high low : DivisionRow 2 lower} (compatible : RadialRowsCompatible lower power high low) :
    RadialRowsCompatible lower power (tangentialRowContraction lower positive power high)
      (tangentialRowContraction lower positive 0 low) := by
  rw [tangentialRowContraction_formula, tangentialRowContraction_formula]
  exact (compatible.cosine.valueMap _).sub (compatible.sine.valueMap _)

end Grad.SourceCollarFullSource
