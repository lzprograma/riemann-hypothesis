module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

section Objects

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

def blockMapC {J : Type} (k₀ : K) (M : Matrix J (ι k₀) ℤ) (z : (Σ k, ι k) → ℂ) : J → ℂ :=
  fun j => ∑ i, (M j i : ℂ) * z ⟨k₀, i⟩

def IsBlockImage {Ω : Type} [Field Ω] {J : Type} [Fintype J] (y : (Σ k, ι k) → Ω) (k₀ : K)
    (M : Matrix J (ι k₀) ℤ) (N : Matrix (ι k₀) J ℤ) (x : J → Ω) : Prop :=
  (∀ j, x j = ∑ i, (M j i : Ω) * y ⟨k₀, i⟩) ∧ ∀ i, y ⟨k₀, i⟩ = ∑ j, (N i j : Ω) * x j

end Objects

theorem BlockSectionsRank.exists_blockBasis {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (k₀ : K) :
    ∃ (r : ℕ) (M : Matrix (Ix (Fin r)) (ι k₀) ℤ) (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) (x : Ix (Fin r) → Ω),
      IsBlockImage y k₀ M N x ∧ LinearIndependent ℤ x := by
  set W : Submodule ℤ Ω := Submodule.span ℤ (Set.range fun i : ι k₀ => y ⟨k₀, i⟩) with hW
  have : Module.Finite ℤ W := Module.Finite.span_of_finite ℤ (Set.finite_range _)
  set b := (Module.Free.chooseBasis ℤ W).reindex (Fintype.equivFin _) with hb
  have hc : ∀ j, ∃ c : ι k₀ → ℤ, ∑ i, c i • y ⟨k₀, i⟩ = (b j : Ω) := fun j =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp (b j).2
  choose c hc using hc
  refine ⟨_, fun j i => c j.2 i, fun i j => b.repr ⟨y ⟨k₀, i⟩, Submodule.subset_span (Set.mem_range_self i)⟩ j.2,
    fun j => (b j.2 : Ω), ⟨fun j => ?_, fun i => ?_⟩, ?_⟩
  · show (b j.2 : Ω) = ∑ i, (c j.2 i : Ω) * y ⟨k₀, i⟩
    rw [← hc j.2]
    simp [zsmul_eq_mul]
  · have h2 := congrArg Subtype.val (b.sum_repr ⟨y ⟨k₀, i⟩, Submodule.subset_span (Set.mem_range_self i)⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    show y ⟨k₀, i⟩ = ∑ j : Ix (Fin _),
      ((b.repr ⟨y ⟨k₀, i⟩, Submodule.subset_span (Set.mem_range_self i)⟩ j.2 : ℤ) : Ω) * (b j.2 : Ω)
    conv_lhs => rw [← h2]
    simp [Fintype.sum_sigma, zsmul_eq_mul]
  · have h1 := b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    refine h1.comp (fun j : Ix (Fin _) => j.2) ?_
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, a'⟩ h
    cases h
    rfl

def BlockImageDatum.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω),
    ∃ (d₀ : HSMBlockDatum D K ι Ω) (r : ℕ) (M : Matrix (Ix (Fin r)) (ι d.k₀) ℤ)
      (N : Matrix (ι d.k₀) (Ix (Fin r)) ℤ) (d' : HSMDatum D Ω (Fin r)),
      d₀.y = d.y ∧ d₀.k₀ = d.k₀ ∧ IsBlockImage d.y d.k₀ M N d'.x ∧
      (∀ z ∈ mcPts (mCoordIdeal d.y), d₀.A.h z = d'.m.ρ (blockMapC d.k₀ M z)) ∧
      ∀ n, blockChi d₀ n = resChi d' n

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
