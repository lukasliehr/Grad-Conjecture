import GC18ClosedMean

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

theorem muCoefficient_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge) :
    FamilyCoherent (muCoefficient admissible gauge) :=
  (identityFamily_coherent L sigma gamma ell 1).add (muDeviation_coherent admissible gauge coherent)

theorem deltaCoefficient_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge) :
    FamilyCoherent (deltaCoefficient admissible gauge) :=
  (identityFamily_coherent L sigma gamma ell 1).add (deltaDeviation_coherent admissible gauge coherent)

theorem liftedEntry_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (row column : Fin 3) (family : CoefficientFamily L sigma gamma ell 1 1) (coherent : FamilyCoherent family) :
    FamilyCoherent (liftedEntry admissible row column family) :=
  (constantFamily_coherent L sigma gamma ell (matrixUnit (input := 1) row 0)).comp admissible
    (coherent.comp admissible (constantFamily_coherent L sigma gamma ell (matrixUnit (output := 1) 0 column)))

theorem liftedEntry_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (row column : Fin 3) (family : CoefficientFamily L sigma gamma ell 1 1) (coherent : FamilyCoherent family)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (liftedEntry admissible row column family) grade angle point =
      Matrix.single row column (familyMatrix family grade angle point 0 0) := by
  have rowCoherent := constantFamily_coherent L sigma gamma ell (matrixUnit (input := 1) row 0)
  have columnCoherent := constantFamily_coherent L sigma gamma ell (matrixUnit (output := 1) 0 column)
  have innerCoherent : FamilyCoherent (composeFamily admissible family
      (constantFamily L sigma gamma ell (matrixUnit (output := 1) 0 column))) :=
    coherent.comp admissible columnCoherent
  unfold liftedEntry
  rw [familyMatrix_comp admissible _ _ rowCoherent innerCoherent,
    familyMatrix_comp admissible _ _ coherent columnCoherent]
  unfold familyMatrix
  rw [constantFamily_physicalValue admissible, constantFamily_physicalValue admissible,
    operatorMatrix_matrixUnit, operatorMatrix_matrixUnit, ← Matrix.mul_assoc,
    Matrix.single_mul_mul_single, one_mul, mul_one]

theorem adjugateFamily_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge) :
    FamilyCoherent (adjugateFamily admissible gauge) :=
  ((((liftedEntry_coherent admissible 0 0 _ (deltaCoefficient_coherent admissible gauge coherent)).add
    (liftedEntry_coherent admissible 1 1 _ (deltaCoefficient_coherent admissible gauge coherent))).add
    (liftedEntry_coherent admissible 2 2 _ (muCoefficient_coherent admissible gauge coherent))).sub
    ((tangentColumn_coherent L sigma gamma ell).comp admissible
      ((etaCoefficient_coherent admissible gauge coherent).comp admissible (scalarRow_coherent L sigma gamma ell)))).sub
    ((scalarColumn_coherent L sigma gamma ell).comp admissible
      ((nuCoefficient_coherent admissible gauge coherent).comp admissible (tangentRow_coherent L sigma gamma ell)))

theorem adjugateFamily_matrix {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (adjugateFamily admissible gauge) grade angle point =
      (Matrix.single 0 0 (familyMatrix (deltaCoefficient admissible gauge) grade angle point 0 0) : Matrix (Fin 3) (Fin 3) ℂ) +
      Matrix.single 1 1 (familyMatrix (deltaCoefficient admissible gauge) grade angle point 0 0) +
      Matrix.single 2 2 (familyMatrix (muCoefficient admissible gauge) grade angle point 0 0) -
      familyMatrix (tangentColumnFamily L sigma gamma ell) grade angle point *
        familyMatrix (etaCoefficient admissible gauge) grade angle point * (Matrix.single 0 2 1 : Matrix (Fin 1) (Fin 3) ℂ) -
      (Matrix.single 2 0 1 : Matrix (Fin 3) (Fin 1) ℂ) * familyMatrix (nuCoefficient admissible gauge) grade angle point *
        familyMatrix (tangentRowFamily L sigma gamma ell) grade angle point := by
  have dc := deltaCoefficient_coherent admissible gauge coherent
  have mc := muCoefficient_coherent admissible gauge coherent
  have ec := etaCoefficient_coherent admissible gauge coherent
  have nc := nuCoefficient_coherent admissible gauge coherent
  have d0 := liftedEntry_coherent admissible 0 0 _ dc
  have d1 := liftedEntry_coherent admissible 1 1 _ dc
  have m2 := liftedEntry_coherent admissible 2 2 _ mc
  have eb : FamilyCoherent (composeFamily admissible (tangentColumnFamily L sigma gamma ell)
      (composeFamily admissible (etaCoefficient admissible gauge) (scalarRowFamily L sigma gamma ell))) :=
    (tangentColumn_coherent L sigma gamma ell).comp admissible (ec.comp admissible (scalarRow_coherent L sigma gamma ell))
  have nb : FamilyCoherent (composeFamily admissible (scalarColumnFamily L sigma gamma ell)
      (composeFamily admissible (nuCoefficient admissible gauge) (tangentRowFamily L sigma gamma ell))) :=
    (scalarColumn_coherent L sigma gamma ell).comp admissible (nc.comp admissible (tangentRow_coherent L sigma gamma ell))
  unfold adjugateFamily
  rw [familyMatrix_sub admissible _ _ (((d0.add d1).add m2).sub eb) nb,
    familyMatrix_sub admissible _ _ ((d0.add d1).add m2) eb,
    familyMatrix_add admissible _ _ (d0.add d1) m2,
    familyMatrix_add admissible _ _ d0 d1,
    liftedEntry_matrix admissible _ _ _ dc, liftedEntry_matrix admissible _ _ _ dc,
    liftedEntry_matrix admissible _ _ _ mc,
    familyMatrix_comp admissible (tangentColumnFamily L sigma gamma ell)
      (composeFamily admissible (etaCoefficient admissible gauge) (scalarRowFamily L sigma gamma ell))
      (tangentColumn_coherent L sigma gamma ell) (ec.comp admissible (scalarRow_coherent L sigma gamma ell)),
    familyMatrix_comp admissible _ _ ec (scalarRow_coherent L sigma gamma ell),
    familyMatrix_comp admissible (scalarColumnFamily L sigma gamma ell)
      (composeFamily admissible (nuCoefficient admissible gauge) (tangentRowFamily L sigma gamma ell))
      (scalarColumn_coherent L sigma gamma ell) (nc.comp admissible (tangentRow_coherent L sigma gamma ell)),
    familyMatrix_comp admissible _ _ nc (tangentRow_coherent L sigma gamma ell)]
  have sr : familyMatrix (scalarRowFamily L sigma gamma ell) grade angle point = Matrix.single 0 2 1 := by
    unfold scalarRowFamily familyMatrix
    rw [constantFamily_physicalValue admissible, operatorMatrix_matrixUnit]
  have sc : familyMatrix (scalarColumnFamily L sigma gamma ell) grade angle point = Matrix.single 2 0 1 := by
    unfold scalarColumnFamily familyMatrix
    rw [constantFamily_physicalValue admissible, operatorMatrix_matrixUnit]
  rw [sr, sc, Matrix.mul_assoc, Matrix.mul_assoc]

theorem operatorMatrix_action {input output : ℕ} (mapping : OperatorValue input output)
    (value : PhysicalValue input) (row : Fin output) :
    mapping value row = ∑ column : Fin input, operatorMatrix mapping row column * value column := by
  conv_lhs => rw [← operatorBasis_expansion value, map_sum]
  change (PiLp.proj 2 (fun _ : Fin output => ℂ) row : PhysicalValue output →L[ℂ] ℂ)
    (∑ column : Fin input, mapping (value column • operatorBasis column)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro column _
  rw [map_smul]
  change value column * operatorMatrix mapping row column = _
  ring

theorem adjugateFamily_action {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) (value : PhysicalValue 3) :
    coefficientPhysicalValue (adjugateFamily admissible gauge grade) angle point value =
      adjugateBlockValue
        (familyMatrix (muCoefficient admissible gauge) grade angle point 0 0)
        (familyMatrix (etaCoefficient admissible gauge) grade angle point 0 0)
        (familyMatrix (nuCoefficient admissible gauge) grade angle point 0 0)
        (familyMatrix (deltaCoefficient admissible gauge) grade angle point 0 0) point value := by
  apply PiLp.ext
  intro row
  rw [operatorMatrix_action]
  change (∑ column : Fin 3, familyMatrix (adjugateFamily admissible gauge) grade angle point row column * value column) = _
  rw [adjugateFamily_matrix admissible gauge coherent, tangentColumn_matrix admissible, tangentRow_matrix admissible]
  fin_cases row <;>
    simp [adjugateBlockValue, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.single_apply] <;> ring_nf
  all_goals simp

end Grad.GaugeCoefficients.Physical.RadialLedger
