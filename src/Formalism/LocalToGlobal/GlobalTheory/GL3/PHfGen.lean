module

public import Formalism.LocalToGlobal.GlobalTheory.GL3.PIopNorm

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

variable {D : D7} {N N' : ℕ}

def Good (D : D7) (w : ℂ) : Prop :=
  ∃ a b : ℤ, Even (a - b) ∧ w = (((a : ℝ) / Real.sqrt D.host.d : ℝ) : ℂ) + (b : ℂ) * Complex.I

theorem Hf_zero_right (T : Tor D) (x : VC D N N') : Hf D T x 0 = 0 := by simp [Hf]

theorem Hf_smul (T : Tor D) (u u' : ℂ) (x y : VC D N N') :
    Hf D T (u • x) (u' • y) = u * starRingEnd ℂ u' * Hf D T x y := by
  unfold Hf
  rw [mul_div_assoc']
  congr 1
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

def genLa (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : Set (VC D N N') :=
  {z | ∃ c ∈ cc, ∃ A ∈ YYl D L L',
    z = (δ * D.host.φ₀ (((c : D.host.K) : D.host.E))) • embV D (tor0 D cc δ) A}

theorem La_le_gen (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    La D (tor0 D cc δ) L L' ≤ AddSubgroup.closure (genLa D cc δ L L') := by
  unfold La
  rw [AddSubgroup.closure_le]
  rintro z ⟨w, hw, A, hA, rfl⟩
  change w ∈ lamOf D cc δ at hw
  unfold lamOf at hw
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨c, hc, A, hA, rfl⟩
  | zero => rw [zero_smul]; exact AddSubgroup.zero_mem _
  | add w w' _ _ h1 h2 => rw [add_smul]; exact AddSubgroup.add_mem _ h1 h2
  | neg w _ h1 => rw [neg_smul]; exact AddSubgroup.neg_mem _ h1

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO

def HfGenRec : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 →
    ∀ N N' (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' →
      ∀ c ∈ cc, ∀ c' ∈ cc, ∀ A ∈ YYl D L L', ∀ B ∈ YYl D L L',
        Good D (δ * D.host.φ₀ (((c : D.host.K) : D.host.E)) *
          starRingEnd ℂ (δ * D.host.φ₀ (((c' : D.host.K) : D.host.E))) *
          Hf D (tor0 D cc δ) (embV D (tor0 D cc δ) A) (embV D (tor0 D cc δ) B))

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
