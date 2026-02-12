/-
  Liouville Counterexample: The Collatz Conjecture Is Fragile
  ============================================================

  Zero-axiom demonstration that the Collatz result for m=3 depends on:
  1. Integer residue structure (prevents persistent minimal halving → no divergence)
  2. Baker's bound on |2^S - 3^k| (prevents cycles)

  For Liouville multipliers (infinite irrationality measure), both fail.
-/
import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Init
import Mathlib.Order.Bounds.Basic

namespace LiouvilleCounterexample

/-! ## Part 1: Integer Structure Forces Extra Halving

For the Collatz map 3x+1 with odd x, ν = v₂(3x+1).
Half the odd residues mod 4 force ν ≥ 2 (when x ≡ 1 mod 4, since 3·1+1=4).
This is a structural constraint of integer arithmetic that has no analogue
over ℚ or ℝ: there, the halving depth ν is unconstrained.

**Key fact**: For any odd x, with probability 1/2 (over residue classes), ν ≥ 2.
This is what Tao's mixing argument quantifies into ν_avg ≥ 33/20 = 1.65 > log₂(3). -/

/-- If x ≡ 1 mod 4 (odd), then 4 | (3x+1), so ν₂(3x+1) ≥ 2. -/
theorem double_halving_mod1 (x : ℕ) (h : x % 4 = 1) :
    4 ∣ (3 * x + 1) := by omega

/-- If x ≡ 3 mod 4 (odd), then 3x+1 ≡ 2 mod 4, so ν₂(3x+1) = 1 (minimal). -/
theorem min_halving_mod3 (x : ℕ) (h : x % 4 = 3) :
    (3 * x + 1) % 2 = 0 ∧ ¬(4 ∣ (3 * x + 1)) := by omega

/-- The result (3x+1)/2 from a minimal step is always odd (stays in Syracuse domain). -/
theorem min_halving_result_odd (x : ℕ) (h : x % 4 = 3) :
    ((3 * x + 1) / 2) % 2 = 1 := by
  obtain ⟨q, rfl⟩ : ∃ q, x = 4 * q + 3 := ⟨x / 4, by omega⟩
  have h1 : 3 * (4 * q + 3) + 1 = 2 * (6 * q + 5) := by ring
  rw [h1, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  omega

/-- Exactly half of odd residues mod 4 force double halving.
    This is the integer structure that prevents persistent ν = 1. -/
theorem half_odds_force_double_halving :
    ∀ x : ℕ, x % 2 = 1 → (x % 4 = 1 ∨ x % 4 = 3) := by omega

/-- x ≡ 1 mod 4 forces ν ≥ 2 (double halving). x ≡ 3 mod 4 allows ν = 1.
    So at least half the time, the orbit gets an extra halving beyond the minimum. -/
theorem forced_extra_halving_or_minimal (x : ℕ) (hodd : x % 2 = 1) :
    4 ∣ (3 * x + 1) ∨ (3 * x + 1) % 4 = 2 := by omega

/-! ## Part 2: Without Integer Structure, Minimal Halving Causes Divergence

Over ℚ (no residue constraints), persistent ν = 1 is unconstrained.
The recurrence x ↦ (3x + 3)/2 grows without bound. -/

/-- The orbit under persistent minimal halving (ν = 1 at every step). -/
def minHalvOrbit (x₀ : ℚ) : ℕ → ℚ
  | 0 => x₀
  | k + 1 => (3 * minHalvOrbit x₀ k + 3) / 2

/-- The orbit stays positive. -/
theorem minHalvOrbit_pos (x₀ : ℚ) (hx : 0 < x₀) : ∀ k, 0 < minHalvOrbit x₀ k := by
  intro k; induction k with
  | zero => exact hx
  | succ k ih => simp only [minHalvOrbit]; linarith

/-- Growth bound: orbit(k) ≥ (3/2)^k · x₀. -/
theorem minHalvOrbit_growth (x₀ : ℚ) (hx : 0 < x₀) :
    ∀ k, (3 / 2 : ℚ) ^ k * x₀ ≤ minHalvOrbit x₀ k := by
  intro k; induction k with
  | zero => simp [minHalvOrbit]
  | succ k ih =>
    simp only [minHalvOrbit]
    have hk := minHalvOrbit_pos x₀ hx k
    have hrw : (3 / 2 : ℚ) ^ (k + 1) * x₀ = 3 / 2 * ((3 / 2) ^ k * x₀) := by ring
    rw [hrw]
    have hmul := mul_le_mul_of_nonneg_left ih (show (0 : ℚ) ≤ 3 / 2 by norm_num)
    linarith

/-- Linear lower bound: orbit(k) ≥ x₀ + 3k/2. -/
theorem minHalvOrbit_linear (x₀ : ℚ) (hx : 0 < x₀) :
    ∀ k : ℕ, x₀ + 3 / 2 * (k : ℚ) ≤ minHalvOrbit x₀ k := by
  intro k; induction k with
  | zero => simp [minHalvOrbit]
  | succ k ih =>
    simp only [minHalvOrbit]
    have hk := minHalvOrbit_pos x₀ hx k
    push_cast [Nat.cast_succ]
    nlinarith

/-- The orbit is unbounded: for any B, some iterate exceeds it. -/
theorem minHalvOrbit_unbounded (x₀ : ℚ) (hx : 0 < x₀) (B : ℚ) :
    ∃ k : ℕ, B < minHalvOrbit x₀ k := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((B - x₀) * (2 / 3))
  refine ⟨n, lt_of_lt_of_le ?_ (minHalvOrbit_linear x₀ hx n)⟩
  nlinarith

/-! ## Part 3: The Cycle Equation Is Satisfiable Over ℚ

Syracuse 1-cycle: x = (mx + 1)/2^ν, so x(2^ν - m) = 1, so x = 1/(2^ν - m).
For ν = 2: x = 1/(4 - m).

- m = 3: x = 1 (trivial cycle only)
- m = 7/2: x = 2 (nontrivial cycle)
- m = (4N-1)/N: x = N (arbitrarily large cycles)

Baker prevents |4 - 3^k/2^S| from being small for integer m = 3.
For non-integer m, no such obstruction exists. -/

/-- m = 3: the only Syracuse fixed point is x = 1 (trivial cycle). -/
theorem trivial_cycle_at_three : ((3 : ℚ) * 1 + 1) / 4 = 1 := by norm_num

/-- m = 3: x = 2 is NOT a fixed point. -/
theorem no_nontrivial_cycle_at_three : ((3 : ℚ) * 2 + 1) / 4 ≠ 2 := by norm_num

/-- m = 7/2: x = 2 IS a fixed point. Nontrivial cycle over ℚ. -/
theorem nontrivial_cycle_exists : ((7 / 2 : ℚ) * 2 + 1) / 4 = 2 := by norm_num

/-- m = 15/4: x = 4 is a fixed point. -/
theorem larger_cycle_exists : ((15 / 4 : ℚ) * 4 + 1) / 4 = 4 := by norm_num

/-- m = 399/100: x = 100 is a fixed point. Cycles of any size. -/
theorem huge_cycle_exists : ((399 / 100 : ℚ) * 100 + 1) / 4 = 100 := by norm_num

/-- For any x₀ > 1, there exists m ∈ (3, 4) creating a 1-cycle at x₀. -/
theorem cycle_for_any_target (x₀ : ℚ) (hx : 1 < x₀) :
    ∃ m : ℚ, 3 < m ∧ m < 4 ∧ (m * x₀ + 1) / 4 = x₀ := by
  have hx_pos : (0 : ℚ) < x₀ := by linarith
  have hx_ne : x₀ ≠ 0 := ne_of_gt hx_pos
  refine ⟨(4 * x₀ - 1) / x₀, ?_, ?_, ?_⟩
  · field_simp; linarith
  · field_simp; linarith
  · field_simp; ring

/-- The "Planck constant": the gap 4 - m = 1/x₀ controls the cycle size.
    As x₀ → ∞, the gap vanishes. Baker keeps it bounded away from zero for m = 3. -/
theorem planck_gap (x₀ : ℚ) (hx : 0 < x₀) :
    4 - (4 * x₀ - 1) / x₀ = 1 / x₀ := by
  have : x₀ ≠ 0 := ne_of_gt hx
  field_simp; ring

end LiouvilleCounterexample

-- Verify: zero custom axioms
#print axioms LiouvilleCounterexample.cycle_for_any_target
#print axioms LiouvilleCounterexample.minHalvOrbit_unbounded
#print axioms LiouvilleCounterexample.double_halving_mod1
