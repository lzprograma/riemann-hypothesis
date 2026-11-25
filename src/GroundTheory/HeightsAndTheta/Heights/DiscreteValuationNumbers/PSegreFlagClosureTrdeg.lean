module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagConeAlg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagClosureTrdeg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PAdjoinTrdegAdd
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairConeLinesIndep
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairBundleTrdeg
import Mathlib.Tactic.TypeStar
public import Mathlib.LinearAlgebra.Matrix.Basis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagClosureTrdeg

theorem sum_flagCoord {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ]
    [Algebra Ω Φ] {N k : ℕ} (hkN : k ≤ N) (w e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ) (a : Fin N → Φ) :
    ∑ j, flagCoord w e t k j * a j =
      ∑ j : Fin k, flagCoord w e t k (Fin.castLE hkN j) * a (Fin.castLE hkN j) := by
  calc ∑ j, flagCoord w e t k j * a j
      = ∑ j ∈ Finset.univ.map (Fin.castLEEmb hkN), flagCoord w e t k j * a j :=
        (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    _ = _ := Finset.sum_map _ _ _
  intro j _ hj
  have hjk : ¬ (j : ℕ) < k := fun h => hj (Finset.mem_map.2 ⟨⟨j, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  simp [flagCoord, hjk]

theorem flagCoord_indep {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ]
    [Algebra Ω Φ] {N k : ℕ} (hkN : k ≤ N) (w e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ)
    (ht : AlgebraicIndependent Ω t) :
    AlgebraicIndependent Ω (fun j : Fin k => flagCoord w e t k (Fin.castLE hkN j)) := by
  classical
  let _ := w.invertibleToMatrix e
  have hS := PairConeLinesIndep.linearChange_indep (w.toMatrix e) (isUnit_of_invertible _) t ht
  have h := hS.comp (Fin.castLE hkN) (Fin.castLE_injective hkN)
  convert h using 1
  funext j
  simp [flagCoord, Module.Basis.toMatrix_apply, j.isLt]

end SegreFlagClosureTrdeg


open SegreFlagClosureTrdeg in
theorem SegreFlagClosureTrdeg.proof (halg : SegreFlagConeAlg.Statement) : SegreFlagClosureTrdeg.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht
    k hk hkN
  obtain ⟨l, m', hl, hm', hal⟩ :=
    halg O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk hkN
  set z := flagClosurePt y w e φ φ' t k with hzdef
  let b := Pi.basisFun Ω (Fin k)
  let ψ : Fin k → Module.Dual Ω (Fin k → Ω) :=
    fun i => b.dualBasis.equivFun.symm (fun j => φ (l i) (w (Fin.castLE hkN j)))
  have hψb : ∀ i j, ψ i (b j) = φ (l i) (w (Fin.castLE hkN j)) := by
    intro i j
    rw [← Module.Basis.dualBasis_equivFun]
    simp [ψ, Finsupp.single_apply]
  have hψ : LinearIndependent Ω ψ := hl.map' b.dualBasis.equivFun.symm.toLinearMap b.dualBasis.equivFun.symm.ker
  have hind' := PairConeLinesIndep.proof Ω Φ K k (Fin k → Ω) b ψ hψ
    (fun j => flagCoord w e t k (Fin.castLE hkN j)) (flagCoord_indep hkN w e t ht) _ hm'
  have hxs : Sum.elim (fun i : Fin k => C (z ⟨some none, l i⟩) * X (some none))
        (fun _ : Unit => (C (z ⟨none, m'⟩) * X none : MvPolynomial (Option (Option K)) Φ)) =
      Sum.elim
        (fun i : Fin k => C (∑ j, flagCoord w e t k (Fin.castLE hkN j) * algebraMap Ω Φ (ψ i (b j))) * X (some none))
        (fun _ : Unit => (C (z ⟨none, m'⟩) * X none : MvPolynomial (Option (Option K)) Φ)) := by
    funext i
    rcases i with i | _
    · simp only [Sum.elim_inl, hψb]
      congr 2
      exact sum_flagCoord hkN w e t _
    · rfl
  rw [← hxs] at hind'
  exact trdeg_pointIdeal_bundle_eq (z := z) hV (fun _ => rfl) AdjoinTrdegAdd.proof hind' hal

end

end GroundTheory.Heights₂.Heights.NumbersDVR
