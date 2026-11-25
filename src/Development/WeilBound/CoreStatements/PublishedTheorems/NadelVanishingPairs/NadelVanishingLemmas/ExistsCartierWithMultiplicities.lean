module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsPrimeCartierDivisor
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

private alias Scheme_ord_one := _root_.GlobalTheory.Cartier.MultEff.ord_one

private alias Scheme_ord_units_inv := _root_.GlobalTheory.Cartier.MultEff.ord_inv

private theorem exists_local_unit_ord_eq_finite_sum {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [DecidableEq X] (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (c : X → ℤ)
    (S : Finset X) (hS : ∀ z ∈ S, Order.coheight z = 1) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ f : (X.functionField)ˣ, ∀ v ∈ U,
      Scheme.ord (f : X.functionField) v = ∑ z ∈ S, if v = z then c z else 0 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨⊤, trivial, 1, fun v _ => by simp [Scheme_ord_one]⟩
  | insert z S hzS ih =>
    obtain ⟨U1, hx1, f1, hf1⟩ := ih (fun w hw => hS w (Finset.mem_insert_of_mem hw))
    obtain ⟨U2, hx2, π, hπ⟩ := PrimeDivCartier.exists_local_eqn X hufd z
      (hS z (Finset.mem_insert_self z S)) x
    refine ⟨U1 ⊓ U2, ⟨hx1, hx2⟩, f1 * π ^ (c z), fun v hv => ?_⟩
    rw [Finset.sum_insert hzS, Units.val_mul, Scheme.ord_mul f1.ne_zero (π ^ c z).ne_zero,
      Units.val_zpow_eq_zpow_val, Scheme.ord_zpow, hf1 v hv.1, hπ v hv.2]
    split_ifs <;> simp [add_comm]

theorem _root_.GlobalTheory.Cartier.CartierDiv.exists_mult_eq_of_locallyFactorial :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X],
      (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ c : X → ℤ,
        (Function.support c).Finite → (∀ z, c z ≠ 0 → Order.coheight z = 1) →
          ∃ D : CartierDiv X, ∀ z, D.mult z = c z := by
  intro X _ _ hufd c hfin hc
  classical
  have : GlobalTheory.IsNormalScheme X :=
    ⟨fun _ => inferInstance, fun x => by have := hufd x; infer_instance⟩
  have hS : ∀ z ∈ hfin.toFinset, Order.coheight z = 1 :=
    fun z hz => hc z (hfin.mem_toFinset.mp hz)
  have hsum : ∀ v, (∑ z ∈ hfin.toFinset, if v = z then c z else 0) = c v := by
    intro v
    rw [Finset.sum_ite_eq]
    split_ifs with hv
    · rfl
    · have : c v = 0 := by
        by_contra h'
        exact hv (hfin.mem_toFinset.mpr h')
      exact this.symm
  choose U hxU f hf using fun x => exists_local_unit_ord_eq_finite_sum hufd c hfin.toFinset hS x
  have hmem : (fun x => germOf x (f x)) ∈ cartierGroup X := by
    intro x
    refine ⟨U x, hxU x, f x, fun y hy => ?_⟩
    rw [germOf_eq_iff]
    have hu := MultEff.unitAt_of_ord y (f x * (f y)⁻¹) fun v hv => by
      rw [Units.val_mul, Scheme.ord_mul (f x).ne_zero ((f y)⁻¹).ne_zero, Scheme_ord_units_inv,
        hf x v (hv.mem_open (U x).isOpen hy), hf y v (hv.mem_open (U y).isOpen (hxU y)), add_neg_cancel]
    simpa [div_eq_mul_inv] using hu
  let D : CartierDiv X := (⟨fun x => germOf x (f x), hmem⟩ : cartierGroup X)
  refine ⟨D, fun z => ?_⟩
  have he : D.IsEqn z (f z) := rfl
  rw [he.mult_eq, hf z z (hxU z), hsum]
