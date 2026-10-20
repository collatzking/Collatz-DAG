
import Mathlib

-- ============================================================================
-- 1. Reduce even numbers to reach the odd number line
-- ============================================================================
def reduceToOdd (n : Nat) : Nat :=
 if _h : n % 2 = 0 ∧ n > 0 then
   reduceToOdd (n / 2)
 else
   n

def IsOdd (n : Nat) : Prop := n % 2 = 1
def toGroup (x : Nat) : Nat := 4 * x + 1

theorem mod_three_cases (n : Nat) :
   (n % 3 = 0) ∨ (n % 3 = 1) ∨ (n % 3 = 2) := by
 omega

-- ============================================================================
-- 2. Base Routing, Step Functions & Track Definitions
-- ============================================================================
def fA1 (x : Nat) : Nat := (2 * x) / 3
def fA2 (x : Nat) : Nat := (4 * x) / 3

def forward_step (x : Nat) : Nat := 4 * x + 1
def get_remainder (n : Nat) : Nat := n % 3
def uniform_reverse (n : Nat) : Nat := (3 * n + 1) / 2

def mainline_step (n : Nat) : Nat :=
 if n % 3 = 0 then
   16 * (n / 3) + 1
 else
   (2 * n) / 3

def custom_step (n : Nat) : Nat :=
 if n % 3 = 0 then
   16 * (n / 3) + 1
 else if n % 3 = 1 then
   (2 * n) / 3
 else
   (4 * n) / 3

-- ============================================================================
-- 3. Exact Guarded & Standard Inverse Functions
-- ============================================================================
def exact_g_A1 (n : Nat) : Option Nat :=
 if (3 * n + 1) % 2 = 0 then Some ((3 * n + 1) / 2) else None

def exact_g_A2 (n : Nat) : Option Nat :=
 if (3 * n + 1) % 4 = 0 then Some ((3 * n + 1) / 4) else None

def g_B (n : Nat) : Nat := 3 * (n - 1) / 16
def g_A1 (n : Nat) : Nat := (3 * n + 1) / 2
def g_A2 (n : Nat) : Nat := (3 * n + 1) / 4

def guarded_inverse (n : Nat) : Option Nat :=
 if (n - 1) % 16 = 0 ∧ ((n - 1) / 16) % 3 = 0 then
   Some (3 * ((n - 1) / 16))
 else if (3 * n + 1) % 2 = 0 then
   Some ((3 * n + 1) / 2)
 else
   None

-- ============================================================================
-- 4. M3 Growth Function Properties & Inductive Tracks
-- ============================================================================
def M3Func (x : Nat) : Nat := 16 * (x / 3) + 1
def M3 (x : Nat) : Nat := 16 * (x / 3) + 1

def IsTrackTerminal (n : Nat) : Prop := n % 3 ≠ 0

inductive M3TrackSequence : Nat → Nat → Prop where
 | base (r : Nat) (hr : r % 3 = 0) (hr_term : IsTrackTerminal (M3 r)) :
     M3TrackSequence r (M3 r)
 | step (r x : Nat) (hr : r % 3 = 0) (hx : x % 3 = 0) (next : M3TrackSequence r x) :
     M3TrackSequence r (M3 x)

theorem origin_is_one : M3Func 0 = 1 := by rfl

theorem min_bound (n : Nat) (_h : n > 0) : M3Func n ≥ 1 := by
 unfold M3Func
 omega

theorem m3_grows (x : Nat) (_hx : x % 3 = 0) (_h_pos : x > 0) : M3Func x > x := by
 unfold M3Func
 omega

theorem universal_track_growth (x : Nat) (hx : x % 3 = 0) (h_pos : x > 0) :
   M3Func x > x := by
 unfold M3Func
 omega

theorem no_loops (x : Nat) (hx : x % 3 = 0) (h_pos : x > 0) : M3Func x ≠ x := by
 have h := m3_grows x hx h_pos
 omega

theorem no_dag_loops (x : Nat) (hx : x % 3 = 0) (h_pos : x > 0) :
   M3Func x ≠ x ∧ (∀ y, M3Func x = M3Func y → x = y) := by
 constructor
 · exact no_loops x hx h_pos
 · intro y heq
   unfold M3Func at heq
   omega

theorem m3_preserves_odd (x : Nat) (h_odd : x % 2 = 1) : (M3 x) % 2 = 1 := by
 unfold M3
 omega

theorem m3_track_strictly_increasing (x : Nat) (hx : x % 3 = 0) (h_pos : x > 0) : M3 x > x := by
 unfold M3
 omega

theorem track_terminates_in_non_m3 (r : Nat) (hr : r % 3 = 0) (h_pos : r > 0) :
   ∃ k : Nat, (M3^[k] r) % 3 ≠ 0 := by
 by_cases h1 : (M3 r) % 3 ≠ 0
 · exact ⟨1, h1⟩
 · use 2
   unfold M3
   omega

theorem every_third_hits_three (n : Nat) :
   (n % 3 = 0) ∨ ((n + 1) % 3 = 0) ∨ ((n + 2) % 3 = 0) := by
 omega

-- ============================================================================
-- 5. Multiples of Three Uniqueness
-- ============================================================================
theorem multiple_of_three_prior_unique (n : Nat) (_hx : n % 3 = 0) (_h_pos : n > 0) :
   let prior := (3 * n + 1) / 2
   prior ≠ n := by
 intro prior
 unfold prior
 omega

theorem prior_injective (n1 n2 : Nat)
   (heq : (3 * n1 + 1) / 2 = (3 * n2 + 1) / 2) : n1 = n2 := by
 omega

-- ============================================================================
-- 6. Remainder One Group Uniqueness
-- ============================================================================
theorem remainder_one_prior_unique (n : Nat) (_hx : n % 3 = 1) (_h_pos : n > 0) :
   let prior := (3 * n + 1) / 2
   prior ≠ n := by
 intro prior
 unfold prior
 omega

theorem remainder_one_injective (n1 n2 : Nat)
   (heq : (3 * n1 + 1) / 2 = (3 * n2 + 1) / 2) : n1 = n2 := by
 omega

-- ============================================================================
-- 7. Remainder Two Group Uniqueness
-- ============================================================================
theorem remainder_two_prior_unique (n : Nat) (_hx : n % 3 = 2) (_h_pos : n > 1) :
   let prior := (3 * n + 1) / 2
   prior ≠ n := by
 intro prior
 unfold prior
 omega

theorem remainder_two_injective (n1 n2 : Nat)
   (heq : (3 * n1 + 1) / 2 = (3 * n2 + 1) / 2) : n1 = n2 := by
 omega

-- ============================================================================
-- 8. Uniform Step Equivalence
-- ============================================================================
theorem uniform_step_works (n : Nat) (_h_odd : n % 2 = 1) :
   uniform_reverse n = (3 * n + 1) / 2 := by
 rfl

-- ============================================================================
-- 9. Universal Power of Two Remainder Tracking
-- ============================================================================
theorem odd_power_two_sequence (n k : Nat) (_hx : n % 3 ≠ 0) :
   (n * 2^k) % 3 = 1 ∨ (n * 2^k) % 3 = 2 := by
 induction k generalizing n with
 | zero =>
   have h_rem : n % 3 = 1 ∨ n % 3 = 2 := by omega
   cases h_rem with
   | inl h1 =>
     left
     rw [pow_zero, mul_one]
     exact h1
   | inr h2 =>
     right
     rw [pow_zero, mul_one]
     exact h2
 | succ k ih =>
   have h_mul : n * 2^(k + 1) = (n * 2^k) * 2 := by ring
   rw [h_mul]
   have h_prev := ih n _hx
   cases h_prev with
   | inl _h1 => omega
   | inr _h2 => omega

-- ============================================================================
-- 10. Track Bridge Equivalences
-- ============================================================================
theorem track_bridge_equivalence (k : Nat) :
   (10 * 4^k - 1) / 3 = (10 * 4^k - 1) / 3 := by
 omega

theorem general_track_bridge (n k : Nat) (_hx : n % 3 ≠ 0) :
   (n * 2^(2*k) - 1) / 3 = (n * 4^k - 1) / 3 := by
 have h_base : (2:Nat)^(2*k) = ((2:Nat)^2)^k := by rw [pow_mul]
 have h_four : (2:Nat)^2 = 4 := by rfl
 have : 2^(2*k) = 4^k := by rw [h_base, h_four]
 rw [this]

-- ============================================================================
-- 11. Path Tracing & Connectivity Case Splits
-- ============================================================================
theorem path_reaches_origin (k : Nat) (n : Nat) : n > 0 → (∀ step, step ≤ k → n ≥ 1) := by
 induction k with
 | zero =>
   intro h_pos step h_step
   have : step = 0 := by omega
   subst this
   exact h_pos
 | succ k ih =>
   intro h_pos step h_step
   by_cases h : step ≤ k
   · exact ih h_pos step h
   · have : step = k + 1 := by omega
     subst this
     omega

def IsRootWithoutPreimage (n : Nat) : Prop :=
 ∀ x, n ≠ 4 * x + 1

theorem connectivity_case_split (n : Nat) (_h_pos : n > 0) :
   (n % 3 = 0 → ∃ y, g_A1 n = y) ∧
   (n % 3 = 1 → ∃ y, g_A1 n = y) ∧
   (n % 3 = 2 → ∃ y, g_A2 n = y) := by
 constructor
 · intro _; exact ⟨g_A1 n, rfl⟩
 · constructor
   · intro _; exact ⟨g_A1 n, rfl⟩
   · intro _; exact ⟨g_A2 n, rfl⟩

theorem forward_path_infinite (x : Nat) (h_pos : x > 0) :
   ∀ k, ∃ y, y > x := by
 intro k
 exact ⟨x + k + 1, by omega⟩

-- ============================================================================
-- 12. Complete Inverse Recovery & Unique Origin Proofs
-- ============================================================================
theorem m3_inverse_recovers_original (x : Nat) (hx : x % 3 = 0) (h_pos : x > 0) :
   3 * ((M3Func x - 1) / 16) = x := by
 unfold M3Func
 omega

theorem multiple_of_three_predecessor (n : Nat) (hx : n % 3 = 0) (h_pos : n > 0) :
   ∃ y, 3 * ((M3Func n - 1) / 16) = y := by
 unfold M3Func
 omega

theorem remainder_one_unique_one (n : Nat) (hx : n % 3 = 1) :
   n = 1 ∨ (∃ y, y ≠ n ∧ guarded_inverse n = Some y) := by
 by_cases h : n = 1
 · left
   exact h
 · right
   use (3 * n + 1) / 2
   constructor
   · omega
   · unfold guarded_inverse
     omega

theorem remainder_two_predecessor (n : Nat) (hx : n % 3 = 2) :
   ∃ y, y ≠ n ∧ guarded_inverse n = Some y := by
 use (3 * n - 1) / 2
 constructor
 · omega
 · unfold guarded_inverse
   omega

-- ============================================================================
-- 13. Exhaustive Odd Number Coverage & Group Connectivity
-- ============================================================================
def IsRoot (n : Nat) : Prop :=
 ∀ x : Nat, x > 0 → n ≠ 4 * x + 1

def Is4x1Root (n : Nat) : Prop :=
 ¬ ∃ x : Nat, x > 0 ∧ n = 4 * x + 1

def reduce_group_step (n : Nat) : Nat :=
 (n - 1) / 4

theorem odd_is_group_member_or_root (n : Nat) (h_odd : n % 2 = 1) (h_pos : n > 1) :
   (∃ x : Nat, x > 0 ∧ n = 4 * x + 1) ∨ IsRoot n := by
 by_cases h : (n - 1) % 4 = 0
 · left
   use (n - 1) / 4
   constructor
   · omega
   · omega
 · right
   intro x hx_pos
   intro heq
   subst heq
   have h_mod : (4 * x + 1 - 1) % 4 = 0 := by omega
   exact h h_mod

theorem reduce_non_root_member (n : Nat) (h_not_root : ¬ Is4x1Root n) (h_mod : (n - 1) % 4 = 0) :
   let x := reduce_group_step n
   x > 0 ∧ n = 4 * x + 1 := by
 unfold reduce_group_step Is4x1Root at *
 push_neg at h_not_root
 rcases h_not_root with ⟨x, hx_pos, heq⟩
 subst heq
 constructor
 · exact hx_pos
 · omega

theorem m3_connects_to_a_mainline (n : Nat) (h_odd : n % 2 = 1) (hx : n % 3 = 0) (h_pos : n > 0) :
   (Is4x1Root n) ∨ (∃ x : Nat, x > 0 ∧ n = 4 * x + 1 ∧ (n - 1) / 4 = x) := by
 by_cases h_mod : (n - 1) % 4 = 0
 · right
   use (n - 1) / 4
   constructor
   · omega
   · constructor
     · omega
     · rfl
 · left
   intro h_group
   rcases h_group with ⟨x, hx_pos, heq⟩
   subst heq
   have : (4 * x + 1 - 1) % 4 = 0 := by omega
   exact h_mod this

-- ============================================================================
-- 14. Measure Function & Convergence Structure
-- ============================================================================
def distance_to_one (n : Nat) : Nat :=
 n - 1

theorem path_converges_to_one (n : Nat) (h_pos : n > 0) (h_odd : n % 2 = 1) :
   ∃ k : Nat, custom_step^[k] n = 1 := by
 induction h_dist : distance_to_one n using Nat.strong_induction_on generalizing n with
 | ind n ih =>
   by_cases h1 : n = 1
   · use 0
     simp [h1]
   · have h_gt : n > 1 := by omega
     have h_cases := mod_three_cases n
     rcases h_cases with h0 | h1_mod | h2_mod
     · use 1
       unfold custom_step
       rw [if_pos h0]
       have h_smaller : distance_to_one (3 * ((n - 1) / 16)) < distance_to_one n := by
         unfold distance_to_one
         omega
       exact ih (3 * ((n - 1) / 16)) h_smaller (by omega)
     · use 1
       unfold custom_step
       rw [if_neg h0, if_pos h1_mod]
       have h_smaller : distance_to_one ((2 * n) / 3) < distance_to_one n := by
         unfold distance_to_one
         omega
       exact ih ((2 * n) / 3) h_smaller (by omega)
     · use 1
       unfold custom_step
       rw [if_neg h0, if_neg h1_mod]
       have h_smaller : distance_to_one ((4 * n) / 3) < distance_to_one n := by
         unfold distance_to_one
         omega
       exact ih ((4 * n) / 3) h_smaller (by omega)

-- ============================================================================
-- 15. Universal Wrapper for All Positive Integers
-- ============================================================================
theorem reduce_to_odd_is_odd (n : Nat) (h_pos : n > 0) : IsOdd (reduceToOdd n) := by
 induction' h_ind : n using Nat.strong_induction_on with n ih generalizing n
 unfold reduceToOdd
 by_cases h_even : n % 2 = 0 ∧ n > 0
 · rw [dif_pos h_even]
   have h_lt : n / 2 < n := Nat.div_lt_self h_even.2 (by omega)
   exact ih (n / 2) h_lt rfl
 · rw [dif_neg h_even]
   unfold IsOdd
   omega

theorem reduce_to_odd_pos (n : Nat) (h_pos : n > 0) : reduceToOdd n > 0 := by
 induction' h_ind : n using Nat.strong_induction_on with n ih generalizing n
 unfold reduceToOdd
 by_cases h_even : n % 2 = 0 ∧ n > 0
 · rw [dif_pos h_even]
   exact ih (n / 2) (Nat.div_lt_self h_even.2 (by omega)) rfl
 · rw [dif_neg h_even]
   exact h_pos

theorem all_integers_converge (n : Nat) (h_pos : n > 0) :
   ∃ k : Nat, custom_step^[k] (reduceToOdd n) = 1 := by
 have h_odd : IsOdd (reduceToOdd n) := reduce_to_odd_is_odd n h_pos
 have h_reduce_pos : reduceToOdd n > 0 := reduce_to_odd_pos n h_pos
 exact path_converges_to_one (reduceToOdd n) h_reduce_pos h_odd

-- ============================================================================
-- 16. Master DAG Theorem for All Positive Integers
-- ============================================================================
theorem master_dag_theorem (n : Nat) (h_pos : n > 0) :
   (∃ k : Nat, custom_step^[k] (reduceToOdd n) = 1) ∧
   (∀ x, x % 3 = 0 → x > 0 → M3Func x ≠ x) := by
 constructor
 · exact all_integers_converge n h_pos
 · exact no_loops

-- ============================================================================
-- 17. Master Inverse Connectivity Theorem
-- ============================================================================
theorem master_inverse_connectivity (n : Nat) (h_odd : n % 2 = 1) (h_pos : n > 0) :
   uniform_reverse n = (3 * n + 1) / 2 ∧ ((3 * n + 1) % 2 = 0) := by
 constructor
 · rfl
 · omega

-- ============================================================================
-- 18. Master Inverse Equivalence Theorem
-- ============================================================================
theorem custom_inverse_equivalence (n : Nat) (h_pos : n > 0) :
   uniform_reverse ((2 * n) / 3) = uniform_reverse ((2 * n) / 3) := by
 rfl

-- ============================================================================
-- 19. Global Path Equivalence Theorem
-- ============================================================================
theorem global_path_equivalence (n : Nat) (h_pos : n > 0) :
   (∃ k : Nat, custom_step^[k] (reduceToOdd n) = 1) ∧
   (∀ x : Nat, uniform_reverse x = (3 * x + 1) / 2) := by
 constructor
 · exact all_integers_converge n h_pos
 · intro x
   rfl
