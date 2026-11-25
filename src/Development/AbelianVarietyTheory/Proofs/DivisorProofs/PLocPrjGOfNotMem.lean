module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroup
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceTwistedConstantTermMatches

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.EulerTw.Transport

open GlobalTheory.BCT

variable {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

theorem map_eq_of_mem (e : G ≃ₜ* H) (A : Subgroup G) (A' : Subgroup H) (h : ∀ g, g ∈ A ↔ e g ∈ A') :
    A' = A.map (e : G →* H) := by
  ext y
  constructor
  · intro hy
    refine ⟨e.symm y, (h _).2 (by simpa using hy), by simp⟩
  · rintro ⟨g, hg, rfl⟩
    exact (h g).1 hg

theorem cptPart_map_equiv (e : G ≃ₜ* H) (T : Subgroup G) :
    cptPart (T.map (e : G →* H)) = (cptPart T).map (e : G →* H) := by
  apply _root_.GlobalTheory.BCT.SplitCtMatch.cptPart_map_equiv' <;> assumption

end GlobalTheory.EulerTw.Transport

namespace GlobalTheory.EulerTw.Transport

open GlobalTheory.BCT GlobalTheory.TwOrbConj

variable {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

theorem twCent_mem (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H) (he : ∀ g, e (θ g) = θ' (e g)) (δ g : G) :
    g ∈ twCent θ δ ↔ e g ∈ twCent θ' (e δ) := by
  rw [mem_twCent, mem_twCent, ← he, ← map_mul, ← map_mul]
  exact e.injective.eq_iff.symm

theorem summand_map (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H) (K : Subgroup G) (K' : Subgroup H) (δ : G)
    (f : G → ℂ) (f' : H → ℂ) (he : ∀ g, e (θ g) = θ' (e g)) (hK : ∀ g, g ∈ K ↔ e g ∈ K')
    (hf : ∀ g, f' (e g) = f g) (y : G) :
    summand θ' K' (e δ) f' (e y) = summand θ K δ f y := by
  apply _root_.GlobalTheory.BCT.SplitCtMatch.summand_map' <;> assumption

end GlobalTheory.EulerTw.Transport

namespace GlobalTheory.EulerTw.Transport

open GlobalTheory.BCT GlobalTheory.TwOrbConj

variable {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

def dcMap (e : G ≃ₜ* H) (T K : Subgroup G) (T' K' : Subgroup H) :
    DoubleCoset.Quotient (T : Set G) (K : Set G) → DoubleCoset.Quotient (T' : Set H) (K' : Set H) :=
  fun q => DoubleCoset.mk T' K' (e (Quotient.out q))

theorem dcMap_bij (e : G ≃ₜ* H) (T K : Subgroup G) (T' K' : Subgroup H) (hT : ∀ g, g ∈ T ↔ e g ∈ T')
    (hK : ∀ g, g ∈ K ↔ e g ∈ K') : Function.Bijective (dcMap e T K T' K') := by
  constructor
  · intro q1 q2 h
    obtain ⟨a, ha, b, hb, hab⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 h
    rw [← DoubleCoset.out_eq' q1, ← DoubleCoset.out_eq' q2, DoubleCoset.eq]
    refine ⟨e.symm a, (hT _).2 (by simpa using ha), e.symm b, (hK _).2 (by simpa using hb), ?_⟩
    apply e.injective
    simp only [map_mul, ContinuousMulEquiv.apply_symm_apply]
    exact hab
  · intro q'
    refine ⟨DoubleCoset.mk T K (e.symm (Quotient.out q')), ?_⟩
    obtain ⟨a, ha, b, hb, hab⟩ := DoubleCoset.mk_out_eq_mul T K (e.symm (Quotient.out q'))
    unfold dcMap
    rw [hab]
    conv_rhs => rw [← DoubleCoset.out_eq' q']
    rw [DoubleCoset.eq]
    refine ⟨(e a)⁻¹, T'.inv_mem ((hT a).1 ha), (e b)⁻¹, K'.inv_mem ((hK b).1 hb), ?_⟩
    simp only [map_mul, ContinuousMulEquiv.apply_symm_apply]
    group

end GlobalTheory.EulerTw.Transport

namespace GlobalTheory.EulerTw.Transport

open GlobalTheory.BCT GlobalTheory.TwOrbConj

theorem twOrb_transport : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H) (K : Subgroup G) (K' : Subgroup H) (δ : G) (f : G → ℂ) (f' : H → ℂ), (∀ g, e (θ g) = θ' (e g)) → (∀ g, g ∈ K ↔ e g ∈ K') → (∀ g, f' (e g) = f g) → twOrb θ K δ f = twOrb θ' K' (e δ) f' := by
  intros
  apply _root_.GlobalTheory.BCT.SplitCtMatch.twOrb_transport' <;> assumption

end GlobalTheory.EulerTw.Transport

namespace GlobalTheory.EulerTw.Inert

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end GlobalTheory.EulerTw.Inert

namespace GlobalTheory.EulerTw.Inert

open GlobalTheory.EulerTw

end GlobalTheory.EulerTw.Inert
