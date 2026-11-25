module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverSchemeGrpObjOfMonoFactor

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_grpObj_isMonHom_of_mono_factor : ∀ (T : Scheme.{0}) (A K : Over T) [GrpObj A] (i : K ⟶ A), Mono i → (∃ m : K ⊗ K ⟶ K, m ≫ i = (i ⊗ₘ i) ≫ μ[A]) → (∃ e : 𝟙_ (Over T) ⟶ K, e ≫ i = η[A]) → (∃ v : K ⟶ K, v ≫ i = i ≫ ι[A]) → ∃ _ : GrpObj K, IsMonHom i := by
  first | exact @GlobalTheory.overScheme_grpObj_of_mono_factor
