module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionCompactEmbedded

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isOpen_alt_bis (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    IsOpen (SncRes.src P p) := by
  apply _root_.GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top.isOpen_alt_bis <;> assumption

theorem chart_coord_ratio : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)), ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P → ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src P p, ∀ p' : (k : K) → ι k, (∀ k, eval (SncRes.coord P p x) (SncRes.lift p ⟨k, p' k⟩) ≠ 0) → ∃ O : Set (SncRes.Pts P), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src P p ∧ ∃ (q : MvPolynomial (Σ k, ι k) ℂ) (F : Fin (Fintype.card (Σ k, ι k)) → MvPolynomial (Σ k, ι k) ℂ), ∀ y ∈ O, (∀ k, eval (SncRes.coord P p y) (SncRes.lift p ⟨k, p' k⟩) ≠ 0) ∧ eval (ReciprocityTheory.AnForm.R.affCoord p' fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) q ≠ 0 ∧ ∀ l, SncRes.coord P p y l * eval (ReciprocityTheory.AnForm.R.affCoord p' fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) q = eval (ReciprocityTheory.AnForm.R.affCoord p' fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) (F l) := by
  intro K _ ι _ P _ p x hx p' hp'
  classical
  have key : ∀ y ∈ SncRes.src P p,
      ((∀ k, eval (SncRes.coord P p y) (SncRes.lift p ⟨k, p' k⟩) ≠ 0) ↔ y ∈ SncRes.src P p') := by
    intro y hy
    simp only [SncRes.eval_lift p y hy, ReciprocityTheory.AnForm.R.affCoord]
    constructor
    · intro h k h0
      exact h k (by simp [h0])
    · intro h k
      exact div_ne_zero (h k) (hy k)
  refine ⟨SncRes.src P p ∩ SncRes.src P p', (isOpen_alt_bis P p).inter (isOpen_alt_bis P p'),
    ⟨hx, (key x hx).1 hp'⟩, Set.inter_subset_left, ∏ k, X ⟨k, p k⟩,
    fun l => X ((Fintype.equivFin (Σ k, ι k)).symm l) *
      ∏ k ∈ Finset.univ.erase ((Fintype.equivFin (Σ k, ι k)).symm l).1, X ⟨k, p k⟩, ?_⟩
  rintro y ⟨hy, hy'⟩
  have hw : (fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) =
      ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) := funext (SncRes.eval_lift p y hy)
  simp only [hw]
  have hone : ∀ k, ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨k, p k⟩ = 1 := fun k => by
    simp [ReciprocityTheory.AnForm.R.affCoord, hy k]
  have hne : ∀ k, ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨k, p' k⟩ ≠ 0 := fun k =>
    div_ne_zero (hy' k) (hy k)
  have ha : ∀ k, ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) ⟨k, p k⟩ ≠ 0 := by
    intro k
    have : ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) ⟨k, p k⟩ =
        1 / ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨k, p' k⟩ := by
      rw [← hone k]; rfl
    rw [this]
    exact div_ne_zero one_ne_zero (hne k)
  refine ⟨(key y hy).2 hy', ?_, fun l => ?_⟩
  · rw [map_prod]
    simp only [eval_X]
    exact Finset.prod_ne_zero_iff.2 fun k _ => ha k
  · set q := (Fintype.equivFin (Σ k, ι k)).symm l with hq
    have hcoord : SncRes.coord P p y l = ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) q := rfl
    rw [map_mul, map_prod, map_prod, hcoord]
    simp only [eval_X]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun k => ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) ⟨k, p k⟩)
      (Finset.mem_univ q.1), ← mul_assoc]
    congr 1
    have h1 : ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) ⟨q.1, p q.1⟩ =
        1 / ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨q.1, p' q.1⟩ := by
      rw [← hone q.1]; rfl
    have h2 : ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) q =
        ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) q /
          ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨q.1, p' q.1⟩ := rfl
    rw [h1, h2, mul_one_div]

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv
