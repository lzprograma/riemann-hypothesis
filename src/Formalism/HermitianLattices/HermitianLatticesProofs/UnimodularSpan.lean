module

public import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic

public section

open NumberField

namespace Formalism.HermitianLatticesTheory

/-- A finitely generated unimodular Hermitian lattice spans its ambient space. -/
theorem IsUnimodular.span_eq_top {K V : Type*} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hU : IsUnimodular h L) (hs : h.IsSymm) (hL : L.FG) :
    Submodule.span K (L : Set V) = ⊤ := by
  obtain ⟨s, rfl⟩ := hL
  apply eq_top_iff.mpr
  intro y _
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples
    (nonZeroDivisors (𝓞 K)) s (h y)
  let aK : K := algebraMap (𝓞 K) K a
  let f := (aK • h y).restrictScalars (𝓞 K)
  have hspan : Submodule.span (𝓞 K) (s : Set V) ≤ (1 : Submodule (𝓞 K) K).comap f := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact Submodule.mem_one.mpr ⟨b, by simpa [f, aK, Algebra.smul_def] using hb⟩
  have hy : star aK • y ∈ Submodule.span (𝓞 K) (s : Set V) := by
    rw [← hU]
    apply (dualBasic_mem_dual _ _ _).mpr
    intro x hx
    obtain ⟨b, hb⟩ := Submodule.mem_one.mp (hspan hx)
    refine Submodule.mem_one.mpr ⟨RingOfIntegers.mapRingHom (starRingEnd K) b, ?_⟩
    change (RingOfIntegers.mapRingHom (starRingEnd K) b : K) = h x (star aK • y)
    change (b : K) = aK * h y x at hb
    rw [RingOfIntegers.mapRingHom_apply, starRingEnd_apply, hb, star_mul, map_smul,
      smul_eq_mul, ← hs.eq x y, starRingEnd_apply, star_star, mul_comm]
  have haK : star aK ≠ 0 :=
    star_ne_zero.mpr ((IsFractionRing.injective (𝓞 K) K).ne (nonZeroDivisors.ne_zero a.2))
  have hy' := (Submodule.span K ((Submodule.span (𝓞 K) (s : Set V)) : Set V)).smul_mem
    (star aK)⁻¹ (Submodule.subset_span hy)
  simpa only [smul_smul, inv_mul_cancel₀ haK, one_smul] using hy'

end Formalism.HermitianLatticesTheory
