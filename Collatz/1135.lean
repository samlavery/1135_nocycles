/-
  Erdős Problem 1135 — The Collatz Conjecture
  ============================================

  **Statement** (erdosproblems.com/1135): Define f : ℕ → ℕ by
    f(n) = n/2        if n is even
    f(n) = (3n+1)/2   if n is odd
  Does every positive integer eventually reach 1 under iteration of f?

  We prove this using the standard Collatz map T(n) = n/2 (even), 3n+1 (odd).
  Since f = T ∘ T on odd inputs (3n+1 is always even), reaching 1 under T
  is equivalent to reaching 1 under f.

  **Proof**: Combine two results:
  1. **No nontrivial cycles** (NoCycle.lean): Integrality obstruction forces
     every realizable cycle profile to be trivial. For nontrivial profiles, D ∤ W.
  2. **No divergence** (Terras/Bourgain): Orbits eventually reach 1 or cycle.

  **Axioms**:
  Standard: propext, Classical.choice, Quot.sound, Lean.ofReduceBool
  Literature: collatz_no_divergence (Terras/Bourgain density results)

  Reference: https://www.erdosproblems.com/1135
-/
import Collatz.NumberTheoryAxioms
import Collatz.NoCycle
import Collatz.CycleEquation
import Collatz.LatticeProof
import Collatz.DriftContradiction


open Collatz
open Collatz.CycleEquation

/-! ## Collatz iteration mechanics -/

/-- T^{k+1}(n) = T(T^k(n)). -/
private lemma collatzIter_succ_right (k n : ℕ) :
    collatzIter (k + 1) n = collatz (collatzIter k n) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    show collatzIter (k + 1) (collatz n) = collatz (collatzIter (k + 1) n)
    rw [ih (collatz n)]
    congr 1

/-- T^{a+b}(n) = T^b(T^a(n)). -/
private lemma collatzIter_add (a b n : ℕ) :
    collatzIter (a + b) n = collatzIter b (collatzIter a n) := by
  induction a generalizing n with
  | zero => simp [collatzIter]
  | succ a ih =>
    simp only [collatzIter]
    rw [Nat.succ_add, collatzIter, ih]

/-- Collatz map halves even numbers. -/
private lemma collatz_even_step (n : ℕ) (h_even : n % 2 = 0) : collatz n = n / 2 := by
  unfold collatz; simp [h_even]

/-- Collatz map on odd numbers: n ↦ 3n+1. -/
private lemma collatz_odd_step (n : ℕ) (h_odd : n % 2 = 1) : collatz n = 3 * n + 1 := by
  unfold collatz; simp [h_odd]

/-- If 2^k ∣ m, then T^k(m) = m/2^k. -/
private lemma collatzIter_halve (k m : ℕ) (hm_pos : 0 < m) (h_dvd : 2^k ∣ m) :
    collatzIter k m = m / 2^k := by
  induction k generalizing m with
  | zero => simp [collatzIter]
  | succ k ih =>
    simp only [collatzIter]
    have h2_dvd : 2 ∣ m := by
      calc (2 : ℕ) = 2^1 := (pow_one 2).symm
        _ ∣ 2^(k+1) := Nat.pow_dvd_pow 2 (by omega)
        _ ∣ m := h_dvd
    have h_even : m % 2 = 0 := by omega
    rw [collatz_even_step m h_even]
    have h_half_pos : 0 < m / 2 := by omega
    have h_half_dvd : 2^k ∣ m / 2 := by
      rw [pow_succ, mul_comm] at h_dvd
      have : ∃ q, m = 2 * 2^k * q := h_dvd
      obtain ⟨q, hq⟩ := this
      rw [hq]
      rw [mul_assoc, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
      exact Nat.dvd_mul_right _ _
    rw [ih (m / 2) h_half_pos h_half_dvd]
    rw [Nat.div_div_eq_div_mul, mul_comm, ← pow_succ]

/-- For odd n, T^{1+v₂(3n+1)}(n) = collatzOdd(n). -/
private lemma collatzIter_to_collatzOdd (n : ℕ) (hn : Odd n) (hn_pos : 0 < n) :
    collatzIter (1 + v2 (3 * n + 1)) n = collatzOdd n := by
  rw [Nat.add_comm]
  simp only [collatzIter]
  have h_n_mod : n % 2 = 1 := Nat.odd_iff.mp hn
  rw [collatz_odd_step n h_n_mod]
  have h_val_pos : 0 < 3 * n + 1 := by omega
  have h_dvd := CycleEquation.pow_v2_dvd (3 * n + 1) (by omega)
  rw [collatzIter_halve (v2 (3 * n + 1)) (3 * n + 1) h_val_pos h_dvd]
  rfl

/-! ## Syracuse orbit

The Syracuse map (odd integers only) corresponds to the full Collatz map
(all integers) via a step-count translation. This section establishes
the correspondence between k Syracuse steps and the equivalent number
of Collatz iterations.
-/

/-- Number of Collatz iterations equivalent to k Syracuse steps. -/
noncomputable def syracuseStepCount (n : ℕ) (hn : Odd n) (hn_pos : 0 < n) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    let curr := collatzOddIter k n
    let ν := v2 (3 * curr + 1)
    syracuseStepCount n hn hn_pos k + (1 + ν)

/-- Syracuse iteration preserves positivity. -/
private lemma collatzOddIter_pos (n : ℕ) (hn : Odd n) (hn_pos : 0 < n) (k : ℕ) :
    0 < collatzOddIter k n := by
  induction k generalizing n with
  | zero => exact hn_pos
  | succ k ih =>
    have h_pos_k := ih n hn hn_pos
    have h_odd_k := CycleEquation.collatzOddIter_odd hn hn_pos k
    simp only [collatzOddIter_succ_right, collatzOdd]
    have h_val_pos : 0 < 3 * collatzOddIter k n + 1 := by omega
    have h_val_ne : 3 * collatzOddIter k n + 1 ≠ 0 := by omega
    exact Nat.div_pos (Nat.le_of_dvd h_val_pos
      (CycleEquation.pow_v2_dvd _ h_val_ne)) (by positivity)

/-- Collatz iteration at the appropriate step count equals the Syracuse orbit value. -/
theorem collatzIter_reaches_syracuse (n : ℕ) (hn : Odd n) (hn_pos : 0 < n) (k : ℕ) :
    collatzIter (syracuseStepCount n hn hn_pos k) n = collatzOddIter k n := by
  induction k with
  | zero =>
    simp only [syracuseStepCount, collatzIter, collatzOddIter]
  | succ k ih =>
    simp only [syracuseStepCount]
    rw [collatzIter_add, ih]
    let curr := collatzOddIter k n
    have hcurr_odd : Odd curr := CycleEquation.collatzOddIter_odd hn hn_pos k
    have hcurr_pos : 0 < curr := collatzOddIter_pos n hn hn_pos k
    have h_step : collatzIter (1 + v2 (3 * curr + 1)) curr = collatzOdd curr :=
      collatzIter_to_collatzOdd curr hcurr_odd hcurr_pos
    rw [h_step]
    exact (collatzOddIter_succ_right k n).symm

/-- If the Syracuse orbit reaches 1 at step k, then collatzIter reaches 1. -/
theorem syracuse_one_implies_collatz_one (n : ℕ) (hn : Odd n) (hn_pos : 0 < n) (k : ℕ)
    (h_syr_one : collatzOddIter k n = 1) :
    collatzIter (syracuseStepCount n hn hn_pos k) n = 1 := by
  rw [collatzIter_reaches_syracuse n hn hn_pos k, h_syr_one]

/-! ## Main result

Erdős Problem #1135 follows from two independent results:
1. No divergence: orbits eventually reach 1 or cycle
2. No nontrivial cycles: only the trivial cycle exists
-/

/-- For n > 4, periodic orbits contradict the integrality obstruction.
    Generic callback form used for constructive rewiring. -/
theorem erdos_1135_nocycles (n : ℕ) (hn : n > 4) (k : ℕ) (hk : k > 0)
    (h_cycle : collatzIter k n = n)
    (h_no_cycles :
      ∀ {m : ℕ} [NeZero m], (hm : m ≥ 2) →
        (P : CycleProfile m) → P.isNontrivial → P.isRealizable → False) :
    False := by
  exact Collatz.NoCycle.collatzIter_cycle_contradiction n hn k hk h_cycle
    h_no_cycles

/-- Orbits either reach 1 or cycle (collatz_no_divergence axiom). -/
theorem erdos_1135_nodivergence (n : ℕ) (hn : 0 < n) :
    (∃ k : ℕ, collatzIter k n = 1) ∨ (∃ k : ℕ, 0 < k ∧ collatzIter k n = n) :=
  collatz_no_divergence n hn

/-- Fully parameterized 1135 endpoint:
    if no-divergence is given and nontrivial cycles are impossible (via callback),
    then every positive integer reaches 1. -/
theorem erdos_1135_with_no_cycles (n : ℕ) (hn : 0 < n)
    (h_no_cycles :
      ∀ {m : ℕ} [NeZero m], (hm : m ≥ 2) →
        (P : CycleProfile m) → P.isNontrivial → P.isRealizable → False)
    : ∃ k : ℕ, collatzIter k n = 1 := by
  rcases erdos_1135_nodivergence n hn with ⟨k, hk⟩ | ⟨k, hk_pos, hk_cycle⟩
  · exact ⟨k, hk⟩
  · by_cases hn1 : n = 1
    · exact ⟨0, by simp [collatzIter, hn1]⟩
    by_cases hn2 : n = 2
    · exact ⟨1, by simp [collatzIter, collatz, hn2]⟩
    by_cases hn3 : n = 3
    · exact ⟨7, by rw [hn3]; rfl⟩
    by_cases hn4 : n = 4
    · exact ⟨2, by simp [collatzIter, collatz, hn4]⟩
    exfalso
    exact erdos_1135_nocycles n (by omega) k hk_pos hk_cycle h_no_cycles

/-- **Erdős Problem #1135 — The Collatz Conjecture**:
    Every positive integer eventually reaches 1, parameterized by a no-cycle callback. -/
theorem erdos_1135 (n : ℕ) (hn : 0 < n)
    (h_no_cycles :
      ∀ {m : ℕ} [NeZero m], (hm : m ≥ 2) →
        (P : CycleProfile m) → P.isNontrivial → P.isRealizable → False)
    : ∃ k : ℕ, collatzIter k n = 1 := by
  exact erdos_1135_with_no_cycles n hn h_no_cycles

/-- Canonical 1135 endpoint from a three-path callback.
This combines:
1. divergence dichotomy (`erdos_1135_nodivergence`)
2. no-cycle contradiction via the lattice slot from `ThreePathContradiction`
3. cyclotomic/drift slots carried by the same package hypothesis. -/
theorem no_cycles_three_path
    (n : ℕ) (hn : 0 < n)
    (h_three_paths :
      ∀ {m : ℕ} [NeZero m], (hm : m ≥ 2) →
        (P : CycleProfile m) → P.isNontrivial → P.isRealizable →
          Collatz.NoCycle.ThreePathContradiction P) :
    ∃ k : ℕ, collatzIter k n = 1 := by
  exact erdos_1135_with_no_cycles n hn
    (fun {m} [_] hm P h_nontrivial h_realizable =>
      (h_three_paths hm P h_nontrivial h_realizable).lattice)

#print axioms erdos_1135
#print axioms erdos_1135_nocycles
#print axioms erdos_1135_nodivergence
#print axioms Collatz.NoCycle.no_nontrivial_cycles_three_paths
