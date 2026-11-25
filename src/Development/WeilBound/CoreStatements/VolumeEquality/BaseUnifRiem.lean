module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsEigenComponentPolynomial
import Mathlib.Tactic.Linter.Style
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.EmbEquivSymmApply

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped TensorProduct

noncomputable section

namespace SheetDecomposition.Riem

open GlobalTheory.CompanionTheory.Ar.Cusp.EigCoef

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem inj (R : RiemLat E g Λ) : Function.Injective R.P :=
  _root_.LevelTowerAlt.precomp_injective R

theorem span_top (R : RiemLat E g Λ) : Submodule.span ℝ (Set.range R.P) = ⊤ :=
  _root_.LevelTowerAlt.span_top R

omit [IsCMField E] in
theorem exists_decomp {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : 𝓞 E →+* Module.End ℂ V) (x : V) :
    ∃ y : (E →+* ℂ) → V, (∀ s, y s ∈ eigSp ρ (s.comp (algebraMap (𝓞 E) E))) ∧ ∑ s, y s = x := by
  classical
  choose cs hcs using fun s => exists_coeff (E := E) s
  have hsum : ∑ s, combo (cs s) = 1 := by
    apply evalHom_injective

    rw [map_sum, map_one]
    simp only [hcs]
    funext s'
    simp [Finset.sum_apply, Pi.single_apply]
  have hmul : ∀ (s : E →+* ℂ) (b : 𝓞 E),
      ((1 : ℂ) ⊗ₜ[ℤ] b) * combo (cs s) = s (algebraMap (𝓞 E) E b) • combo (cs s) := by
    intro s b
    apply evalHom_injective
    rw [map_mul, map_smul, hcs]
    funext s'
    by_cases h : s' = s
    · subst h
      simp [evalHom_tmul]
    · simp [evalHom_tmul, h]
  refine ⟨fun s => actHom ρ (combo (cs s)) x, fun s => mem_eigSp_iff.2 fun b => ?_, ?_⟩
  · have h := congrArg (actHom ρ) (hmul s b)
    rw [map_mul, map_smul, actHom_tmul, one_smul] at h
    exact LinearMap.congr_fun h x
  · have h := congrArg (actHom ρ) hsum

    rw [map_sum, map_one] at h
    have h2 := LinearMap.congr_fun h x
    simpa [LinearMap.sum_apply] using h2

omit [IsCMField E] in
theorem exists_proj {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : 𝓞 E →+* Module.End ℂ V) (s : 𝓞 E →+* ℂ) :
    ∃ p : V →ₗ[ℂ] V, (∀ x, eigComp ρ s x = p x) ∧ (∀ x, p x ∈ eigSp ρ s) ∧ (∀ x ∈ eigSp ρ s, p x = x) ∧
      ∀ a x, p (ρ a x) = s a • p x := by
  exact ⟨_root_.LevelTowerAlt.proj ρ s, _root_.LevelTowerAlt.eigComp_eq ρ s,
    _root_.LevelTowerAlt.proj_mem ρ s, fun _ hx => _root_.LevelTowerAlt.proj_eig_self hx,
    _root_.LevelTowerAlt.proj_act ρ s⟩

omit [IsCMField E] in
theorem sum_eigComp {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : 𝓞 E →+* Module.End ℂ V) (x : V) :
    ∑ s : E →+* ℂ, eigComp ρ (s.comp (algebraMap (𝓞 E) E)) x = x := by
  exact (Fintype.sum_equiv (_root_.LevelTowerAlt.embEquiv E) _
    (fun t => _root_.LevelTowerAlt.proj ρ t x)
    fun s => _root_.LevelTowerAlt.eigComp_eq ρ _ x).trans (_root_.LevelTowerAlt.sum_proj ρ x)

theorem orth (R : RiemLat E g Λ) (s s' : 𝓞 E →+* ℂ) (hne : s ≠ s') (x : Fin g → ℂ) (hx : x ∈ eigSp R.B s)
    (y : Fin g → ℂ) (hy : y ∈ eigSp R.B s') : R.ip x y = 0 := by
  exact _root_.LevelTowerAlt.ip_orth R hne hx hy

end SheetDecomposition.Riem

namespace SheetDecomposition

theorem riemBasic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ), Function.Injective R.P ∧ Submodule.span ℝ (Set.range R.P) = ⊤ ∧ (∀ s : 𝓞 E →+* ℂ, (∀ x, eigComp R.B s x ∈ eigSp R.B s) ∧ (∀ x ∈ eigSp R.B s, eigComp R.B s x = x) ∧ (∀ (c : ℂ) x y, eigComp R.B s (c • x + y) = c • eigComp R.B s x + eigComp R.B s y) ∧ ∀ a x, eigComp R.B s (R.B a x) = s a • eigComp R.B s x) ∧ (∀ x, ∑ s : E →+* ℂ, eigComp R.B (s.comp (algebraMap (𝓞 E) E)) x = x) ∧ ∀ s s' : 𝓞 E →+* ℂ, s ≠ s' → ∀ x ∈ eigSp R.B s, ∀ y ∈ eigSp R.B s', R.ip x y = 0 := by
  intro E _ _ _ g Λ _ _ Ψ _ R
  refine ⟨Riem.inj R, Riem.span_top R, fun s => ?_, Riem.sum_eigComp R.B, Riem.orth R⟩
  obtain ⟨p, h₁, h₂, h₃, h₄⟩ := Riem.exists_proj R.B s
  simp only [h₁]
  exact ⟨h₂, h₃, fun c x y => by rw [map_add (f := _), map_smul], h₄⟩

end SheetDecomposition
