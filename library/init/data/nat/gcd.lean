/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro

Definitions and properties of gcd, lcm, and coprime.
-/
prelude
import init.data.nat.lemmas init.meta.well_founded_tactics

open well_founded

namespace nat

/- gcd -/

def gcd : nat → nat → nat
| 0        y := y
| (succ x) y := have y % succ x < succ x, from mod_lt _ $ succ_pos _,
                gcd (y % succ x) (succ x)

/-* Let $x$ be a natural number, then gcd of 0 and $x$ is $x$. *-/
@[simp] theorem gcd_zero_left (x : nat) : gcd 0 x = x := by simp [gcd]

@[simp] theorem gcd_succ (x y : nat) : gcd (succ x) y = gcd (y % succ x) (succ x) :=
by simp [gcd]

/-* Let $n$ be a natural number, then gcd of 1 and $x$ is 1. *-/
@[simp] theorem gcd_one_left (n : ℕ) : gcd 1 n = 1 := by simp [gcd]

/-* Let $x, y$ be two natural numbers, then gcd of $x$ and $y$ is y if $x = 0$,
or else gcd of $y % x$ and $x$. *-/
theorem gcd_def (x y : ℕ) : gcd x y = if x = 0 then y else gcd (y % x) x :=
by cases x; simp [gcd, succ_ne_zero]

/-* gcd of $n$ and $n$ is $n$. *-/
@[simp] theorem gcd_self (n : ℕ) : gcd n n = n :=
by cases n; simp [gcd, mod_self]

/-* gcd of $n$ and 0 is $n$. *-/
@[simp] theorem gcd_zero_right (n : ℕ) : gcd n 0 = n :=
by cases n; simp [gcd]

/-* gcd of $m$ and $n$ equals to gcd of $(n % m)$ and $m$. *-/
theorem gcd_rec (m n : ℕ) : gcd m n = gcd (n % m) m :=
by cases m; simp [gcd]

@[elab_as_eliminator]
theorem gcd.induction {P : ℕ → ℕ → Prop}
                   (m n : ℕ)
                   (H0 : ∀n, P 0 n)
                   (H1 : ∀m n, 0 < m → P (n % m) m → P m n) :
                 P m n :=
@induction _ _ lt_wf (λm, ∀n, P m n) m (λk IH,
  by {induction k with k ih, exact H0,
      exact λn, H1 _ _ (succ_pos _) (IH _ (mod_lt _ (succ_pos _)) _)}) n

/-* Let $m, n$ be two integers, then lcm of $m$ and $n$ equals to $m * n$ over gcd of $m$ and $n$. *-/
def lcm (m n : ℕ) : ℕ := m * n / (gcd m n)

@[reducible] def coprime (m n : ℕ) : Prop := gcd m n = 1

end nat
