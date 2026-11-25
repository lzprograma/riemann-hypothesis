module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
public import Mathlib.Algebra.DualNumber
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer

noncomputable section

namespace GlobalTheory.AnPer.Hol

def jet {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} {p : E} (hp : p ∈ W) (v : E) :
    Hol W →ₐ[ℂ] DualNumber ℂ where
  toFun h := TrivSqZeroExt.inl (ev p hp h) + TrivSqZeroExt.inr (ev p hp (der v h))
  map_one' := by
    ext <;> simp
  map_mul' f g := by
    ext
    · simp
    · simp [Derivation.leibniz]; ring
  map_zero' := by
    ext <;> simp
  map_add' f g := by
    ext <;> simp
  commutes' c := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem jet_spec {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} {p : E} (hp : p ∈ W)
    (v : E) (h : Hol W) : (jet hp v h).fst = h.fn p ∧ (jet hp v h).snd = fderiv ℂ h.fn p v := by
  constructor
  · change (TrivSqZeroExt.inl (ev p hp h) + TrivSqZeroExt.inr (ev p hp (der v h)) : DualNumber ℂ).fst = _
    simp [ev_apply]
  · change (TrivSqZeroExt.inl (ev p hp h) + TrivSqZeroExt.inr (ev p hp (der v h)) : DualNumber ℂ).snd = _
    simp [ev_apply, fn_der v h hp]

end GlobalTheory.AnPer.Hol

theorem GlobalTheory.AnPer.Hol.exists_jet_algHom : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) (p : E), p ∈ W → ∀ v : E, ∃ ρ : Hol W →ₐ[ℂ] DualNumber ℂ, ∀ h, (ρ h).fst = h.fn p ∧ (ρ h).snd = fderiv ℂ h.fn p v := by
  intro E _ _ W p hp v
  exact ⟨GlobalTheory.AnPer.Hol.jet hp v, GlobalTheory.AnPer.Hol.jet_spec hp v⟩
