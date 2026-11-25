module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

@[expose] public section

noncomputable section

open MeasureTheory Matrix ValuativeRel NumberField
open scoped NNReal Topology

namespace GlobalTheory.WeilM.SiegelModel

section Alg

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]

variable [Invertible (2 : R)]


omit [DecidableEq α] in
theorem rho_diag (ψ : AddChar R ℂ) {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d : Darboux (symp c ξ JA JB) κ}
    {dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)} (h : IsDblCoord c ξ JA JB d dd) (z : Matrix α β E)
    (φ : (κ ⊕ κ → R) → ℂ) (u : κ → R) :
    dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β E)ᵀ) φ (Sum.elim u u) = φ (Sum.elim (u + (d.e z).1) (u + (d.e z).1)) := by
  rw [diagCols, transpose_fromRows, mul_fromCols, transpose_one, Matrix.mul_one, Darboux.rho, h, schr]
  have e : (Sum.elim u u + Sum.elim (d.e z).1 (d.e z).1 : κ ⊕ κ → R) = Sum.elim (u + (d.e z).1) (u + (d.e z).1) := by
    ext (k | k) <;> rfl
  simp [sumElim_dotProduct_sumElim, e]

end Alg


end GlobalTheory.WeilM.SiegelModel
end
