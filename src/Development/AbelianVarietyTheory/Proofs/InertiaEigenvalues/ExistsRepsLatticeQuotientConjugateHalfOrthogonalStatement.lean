module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasShape
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepsLatticeQuotientConjugateHalfOrthogonal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisOAdd
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

theorem _root_.GlobalTheory.T.exists_reps_latticeQuotient_conjugateHalf_orthogonal : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, a * a = a → infPart D a = 0 → ∀ k : ℕ, 0 < k → ∃ Y : Finset (WO S T), Y.Nonempty ∧ (∀ y ∈ Y, IsHalf (cA D a) y ∧ k • y ∈ latH S T ΛS ΛT) ∧ (∀ y', IsHalf (cA D a) y' → k • y' ∈ latH S T ΛS ΛT → ∃! y, y ∈ Y ∧ ∃ u ∈ latH S T ΛS ΛT, IsHalf (cA D a) u ∧ y' - y = k • u) ∧ ∀ x, IsHalf a x → k • x ∈ latH S T ΛS ΛT → ((∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ x = k • u) → ∀ y ∈ Y, ψ (symplO S T x y) = 1) ∧ ((¬ ∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ x = k • u) → ∑ y ∈ Y, ψ (symplO S T x y) = 0) := by
  first | exact @GlobalTheory.DownLift.GenQuot.reps_orth
