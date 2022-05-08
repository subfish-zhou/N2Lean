/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/
prelude
import init.logic

notation `ℕ` := nat

namespace nat

inductive less_than_or_equal (a : ℕ) : ℕ → Prop
| refl : less_than_or_equal a
| step : Π {b}, less_than_or_equal b → less_than_or_equal (succ b)

instance : has_le ℕ :=
⟨nat.less_than_or_equal⟩

@[reducible] protected def le (n m : ℕ) := nat.less_than_or_equal n m
@[reducible] protected def lt (n m : ℕ) := nat.less_than_or_equal (succ n) m

instance : has_lt ℕ :=
⟨nat.lt⟩

def pred : ℕ → ℕ
| 0     := 0
| (a+1) := a

protected def sub : ℕ → ℕ → ℕ
| a 0     := a
| a (b+1) := pred (sub a b)

protected def mul : nat → nat → nat
| a 0     := 0
| a (b+1) := (mul a b) + a

instance : has_sub ℕ :=
⟨nat.sub⟩

instance : has_mul ℕ :=
⟨nat.mul⟩

-- defeq to the instance provided by comm_semiring
instance : has_dvd ℕ :=
has_dvd.mk (λ a b, ∃ c, b = a * c)

instance : decidable_eq ℕ
| zero     zero     := is_true rfl
| (succ x) zero     := is_false (λ h, nat.no_confusion h)
| zero     (succ y) := is_false (λ h, nat.no_confusion h)
| (succ x) (succ y) :=
    match decidable_eq x y with
    | is_true xeqy := is_true (xeqy ▸ eq.refl (succ x))
    | is_false xney := is_false (λ h, nat.no_confusion h (λ xeqy, absurd xeqy xney))
    end

def {u} repeat {α : Type u} (f : ℕ → α → α) : ℕ → α → α
| 0         a := a
| (succ n)  a := f n (repeat n a)

instance : inhabited ℕ :=
⟨nat.zero⟩

@[simp] lemma nat_zero_eq_zero : nat.zero = 0 :=
rfl

/- properties of inequality -/
/-* For any natural number $a$, $a \leq a$. *-/
@[refl] protected lemma le_refl (a : ℕ) : a ≤ a :=
less_than_or_equal.refl

/-* For any natural number $n$, it is lower or equal to its succession. *-/
lemma le_succ (n : ℕ) : n ≤ succ n :=
less_than_or_equal.step (nat.le_refl n)

/-* Let $n, m$ be two natural numbers, then the succession of $n$ is lower or equal to the succession of $m$. *-/
lemma succ_le_succ {n m : ℕ} : n ≤ m → succ n ≤ succ m :=
λ h, less_than_or_equal.rec (nat.le_refl (succ n)) (λ a b, less_than_or_equal.step) h

/-* If $n$ is a natural number, then $0 \leq n$. *-/
protected lemma zero_le : ∀ (n : ℕ), 0 ≤ n
| 0     := nat.le_refl 0
| (n+1) := less_than_or_equal.step (zero_le n)

/-* If $n$ is a natural number, then 0 is lower than the succession of $n$. *-/
lemma zero_lt_succ (n : ℕ) : 0 < succ n :=
succ_le_succ n.zero_le

lemma succ_pos (n : ℕ) : 0 < succ n := zero_lt_succ n

lemma not_succ_le_zero : ∀ (n : ℕ), succ n ≤ 0 → false
.

protected lemma not_lt_zero (a : ℕ) : ¬ a < 0 := not_succ_le_zero a

lemma pred_le_pred {n m : ℕ} : n ≤ m → pred n ≤ pred m :=
λ h, less_than_or_equal.rec_on h
  (nat.le_refl (pred n))
  (λ n, nat.rec (λ a b, b) (λ a b c, less_than_or_equal.step) n)

/-* Let $n, m$ be natural numbers, then that the succession of $n$ is lower or equal to the succession of $m$ implies $n \leq m$. *-/
lemma le_of_succ_le_succ {n m : ℕ} : succ n ≤ succ m → n ≤ m :=
pred_le_pred

instance decidable_le : ∀ a b : ℕ, decidable (a ≤ b)
| 0     b     := is_true b.zero_le
| (a+1) 0     := is_false (not_succ_le_zero a)
| (a+1) (b+1) :=
  match decidable_le a b with
  | is_true h  := is_true (succ_le_succ h)
  | is_false h := is_false (λ a, h (le_of_succ_le_succ a))
  end

instance decidable_lt : ∀ a b : ℕ, decidable (a < b) :=
λ a b, nat.decidable_le (succ a) b

/-* Let $a, b$ be two natural numbers, and $a \leq b$, then $a = b$ or $a < b$. *-/
protected lemma eq_or_lt_of_le {a b : ℕ} (h : a ≤ b) : a = b ∨ a < b :=
less_than_or_equal.cases_on h (or.inl rfl) (λ n h, or.inr (succ_le_succ h))

/-* Let $a, b$ be two natural numbers, then $a \leq b$ implies $a$ is lower than the succesion of $b$. *-/
lemma lt_succ_of_le {a b : ℕ} : a ≤ b → a < succ b :=
succ_le_succ

/-* Let $a, b$ be two natural numbers, then the subtraction of the successions of $a$ and $b$ equals to $a - b$. *-/
@[simp] lemma succ_sub_succ_eq_sub (a b : ℕ) : succ a - succ b = a - b :=
nat.rec_on b
  (show succ a - succ zero = a - zero, from (eq.refl (succ a - succ zero)))
  (λ b, congr_arg pred)

lemma not_succ_le_self : ∀ n : ℕ, ¬succ n ≤ n :=
λ n, nat.rec (not_succ_le_zero 0) (λ a b c, b (le_of_succ_le_succ c)) n

protected lemma lt_irrefl (n : ℕ) : ¬n < n :=
not_succ_le_self n

/-* Let $n, m, k$ be natural numbers, and $n \leq m$, then $m \leq k$ implies $n \leq k$. *-/
protected lemma le_trans {n m k : ℕ} (h1 : n ≤ m) : m ≤ k → n ≤ k :=
less_than_or_equal.rec h1 (λ p h2, less_than_or_equal.step)

lemma pred_le : ∀ (n : ℕ), pred n ≤ n
| 0        := less_than_or_equal.refl
| (succ a) := less_than_or_equal.step less_than_or_equal.refl

lemma pred_lt : ∀ {n : ℕ}, n ≠ 0 → pred n < n
| 0        h := absurd rfl h
| (succ a) h := lt_succ_of_le less_than_or_equal.refl

/-* Let $a, b$ be natural numbers, then $a - b \leq b$. *-/
protected lemma sub_le (a b : ℕ) : a - b ≤ a :=
nat.rec_on b (nat.le_refl (a - 0)) (λ b₁, nat.le_trans (pred_le (a - b₁)))

/-* Let $a, b$ be natural numbers, then $0 < a$ and $0 < b$ imply $a - b < a$. *-/
protected lemma sub_lt : ∀ {a b : ℕ}, 0 < a → 0 < b → a - b < a
| 0     b     h1 h2 := absurd h1 (nat.lt_irrefl 0)
| (a+1) 0     h1 h2 := absurd h2 (nat.lt_irrefl 0)
| (a+1) (b+1) h1 h2 :=
  eq.symm (succ_sub_succ_eq_sub a b) ▸
    show a - b < succ a, from
    lt_succ_of_le (a.sub_le b)

/-* Let $n, m, k$ be naturla numbers, then $n < m$ and $m \leq k$ imply $n < k$. *-/
protected lemma lt_of_lt_of_le {n m k : ℕ} : n < m → m ≤ k → n < k :=
nat.le_trans

/- Basic nat.add lemmas -/
protected lemma zero_add : ∀ n : ℕ, 0 + n = n
| 0     := rfl
| (n+1) := congr_arg succ (zero_add n)

/-* Let $n, m$ be natural numbers, then the succession of $n$ plus $m$ equals to the succession of $(n + m)$. *-/
lemma succ_add : ∀ n m : ℕ, (succ n) + m = succ (n + m)
| n 0     := rfl
| n (m+1) := congr_arg succ (succ_add n m)

/-* Let $n, m$ be natural numbers, then $n$ plus the succession of $m$ equals to the succession of $(n + m)$. *-/
lemma add_succ (n m : ℕ) : n + succ m = succ (n + m) :=
rfl

protected lemma add_zero (n : ℕ) : n + 0 = n :=
rfl

/-* Let $n$ be a natural number, then $n + 1$ equals to its succession. *-/
lemma add_one (n : ℕ) : n + 1 = succ n :=
rfl

/-* Let $n$ be a natural number, then the succesion of $n$ equals to $n + 1$. *-/
lemma succ_eq_add_one (n : ℕ) : succ n = n + 1 :=
rfl

/- Basic lemmas for comparing numerals -/

protected lemma bit0_succ_eq (n : ℕ) : bit0 (succ n) = succ (succ (bit0 n)) :=
show succ (succ n + n) = succ (succ (n + n)), from
congr_arg succ (succ_add n n)

protected lemma zero_lt_bit0 : ∀ {n : nat}, n ≠ 0 → 0 < bit0 n
| 0        h := absurd rfl h
| (succ n) h :=
  calc 0 < succ (succ (bit0 n)) : zero_lt_succ _
     ... = bit0 (succ n)        : (nat.bit0_succ_eq n).symm

protected lemma zero_lt_bit1 (n : nat) : 0 < bit1 n :=
zero_lt_succ _

protected lemma bit0_ne_zero : ∀ {n : ℕ}, n ≠ 0 → bit0 n ≠ 0
| 0     h := absurd rfl h
| (n+1) h :=
  suffices (n+1) + (n+1) ≠ 0, from this,
  suffices succ ((n+1) + n) ≠ 0, from this,
  λ h, nat.no_confusion h

protected lemma bit1_ne_zero (n : ℕ) : bit1 n ≠ 0 :=
show succ (n + n) ≠ 0, from
λ h, nat.no_confusion h

end nat
