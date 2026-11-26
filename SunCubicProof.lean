import Mathlib

namespace SunCubic

def entry (m n j : ℕ) : ℤ :=
  if j ≤ n then (Nat.choose (n + j) j : ℤ) ^ m else 0

def prodCoeff (m a b d : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (d + 1), entry m a j * entry m b (d - j)

def delta (m n d : ℕ) : ℤ :=
  prodCoeff m (n - 1) (n + 1) d - prodCoeff m n n d

noncomputable def R (m n : ℕ) : Polynomial ℤ := ∑ j ∈ Finset.range (n + 1),
  Polynomial.monomial j ((Nat.choose (n + j) j : ℤ) ^ m)

theorem coeffR (m n j : ℕ) : (R m n).coeff j = entry m n j := by
  classical
  unfold R
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  simp [Finsupp.single_apply, entry]

theorem coeffProduct (m a b d : ℕ) : (R m a * R m b).coeff d = prodCoeff m a b d := by
  simp only [Polynomial.coeff_mul, coeffR, prodCoeff]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => entry m a i * entry m b j) d

theorem coeffDelta (m n d : ℕ) :
    (R m (n - 1) * R m (n + 1) - (R m n)^2).coeff d = delta m n d := by
  rw [Polynomial.coeff_sub, pow_two, coeffProduct, coeffProduct, delta]

def Conjecture : Prop := ∀ n d : ℕ, 1 ≤ n → 0 ≤ delta 3 n d

theorem constantCoeff (n : ℕ) : delta 3 n 0 = 0 := by
  simp [delta, prodCoeff, entry]

theorem linearInterior (k : ℕ) : delta 3 (k + 2) 1 = 6 * ((k : ℤ) + 3) := by
  simp [delta, prodCoeff, Finset.sum_range_succ, entry, Nat.choose_one_right, Nat.cast_add]
  ring

theorem linearPositive (n : ℕ) (hn : 1 ≤ n) : 0 < delta 3 n 1 := by
  rcases n with _ | n
  · omega
  rcases n with _ | k
  · decide
  · rw [linearInterior]; positivity

private theorem chooseTwoQ (k : ℕ) : ((Nat.choose (k + 2) 2 : ℕ) : ℚ) = ((k : ℚ) + 2) * (k + 1) / 2 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by omega, Nat.choose_succ_succ]
    push_cast
    rw [ih, Nat.choose_one_right]
    push_cast
    ring

theorem quadraticInterior (k : ℕ) : (8 : ℚ) * (delta 3 (k + 3) 2 : ℚ) =
    6 * (k : ℚ)^4 + 156 * k^3 + 1386 * k^2 + 5172 * k + 6960 := by
  simp [delta, prodCoeff, Finset.sum_range_succ, entry, Nat.choose_one_right]
  simp only [chooseTwoQ]
  push_cast
  ring

theorem quadraticPositive (n : ℕ) (hn : 1 ≤ n) : 0 < delta 3 n 2 := by
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · decide
  rcases n with _ | k
  · decide
  · have h := quadraticInterior k
    have hr : 0 < 6 * (k : ℚ)^4 + 156*k^3 + 1386*k^2 + 5172*k + 6960 := by positivity
    rw [← h] at hr
    have hp : (0 : ℚ) < (delta 3 (k + 3) 2 : ℚ) := by linarith
    exact_mod_cast hp

theorem lowDegrees (n d : ℕ) (hn : 1 ≤ n) (hd : d ≤ 2) :
    0 ≤ (R 3 (n - 1) * R 3 (n + 1) - (R 3 n)^2).coeff d := by
  rw [coeffDelta]
  interval_cases d
  · rw [constantCoeff]
  · exact (linearPositive n hn).le
  · exact (quadraticPositive n hn).le

end SunCubic

namespace Cone

def w (n d j : ℕ) : ℚ := ((Nat.choose (n-1+j) j : ℚ) * (Nat.choose (n-1+(d-j)) (d-j) : ℚ)) ^ 3

def xval (d j : ℕ) : ℚ := (j : ℚ) - (d : ℚ)/2

def F (n b s : ℚ) : ℚ :=
  let a := n+b
  let T := a*(a+1)
  let V := 2*a+1
  n^3*((T+s)^3+3*(T+s)*V^2*s)-(n+1)^3*(a^2-s)^3

def Z (n b s : ℚ) : ℚ :=
  let a := n+b
  6*n*s*(a*b-s)^2+2*n^3*s^2-(a*b-s)^3-3*n^2*s*(a*b-s)

def K (n b : ℚ) : ℚ :=
  let a := n+b
  let U := n*(a+1)
  let W := (n+1)*a
  U^2 + U*W + W^2

set_option maxHeartbeats 4000000 in
theorem pointwise (n b s : ℚ) (hb : 0 < b) (hl : 2*b ≤ n) (hu : n ≤ 6*b)
    (hs : 0 ≤ s) (hs' : s ≤ b^2) : 0 ≤ b^2 * F n b s - K n b * Z n b s := by
  let a := n+b
  let T := a*(a+1)
  let V := 2*a+1
  let B := b^2*(3*n^3*T^2+3*n^3*V^2*T+3*(n+1)^3*a^4) -
    K n b*((6*n+3)*(a*b)^2-3*n^2*a*b)
  let C := b^2*(3*n^3*(T+V^2)-3*(n+1)^3*a^2) -
    K n b*(-12*n*a*b+2*n^3-3*a*b+3*n^2)
  let D := b^2*(n^3+(n+1)^3)-K n b*(6*n+1)
  let u := (n-2*b)/4
  let v := (6*b-n)/4
  have hU : 0 ≤ u := by dsimp [u]; linarith
  have hV : 0 ≤ v := by dsimp [v]; linarith
  have hb' : b = u+v := by dsimp [u,v]; ring
  have hn' : n = 6*u+2*v := by dsimp [u,v]; ring
  have hB : 0 ≤ B := by
    dsimp only [B,T,V,a,K]
    rw [hn',hb']
    ring_nf
    positivity
  have hC : 0 ≤ 2*B+C*b^2 := by
    dsimp only [B,C,T,V,a,K]
    rw [hn',hb']
    ring_nf
    positivity
  have hD : 0 ≤ B+C*b^2+D*b^4 := by
    dsimp only [B,C,D,T,V,a,K]
    rw [hn',hb']
    ring_nf
    positivity
  have hgap : 0 ≤ b^2-s := by linarith
  have hpos : 0 ≤ s*(B*(b^2-s)^2 + (2*B+C*b^2)*s*(b^2-s) + (B+C*b^2+D*b^4)*s^2) := by
    positivity
  have heq : b^4*(b^2*F n b s-K n b*Z n b s) =
      s*(B*(b^2-s)^2+(2*B+C*b^2)*s*(b^2-s)+(B+C*b^2+D*b^4)*s^2) := by
    dsimp only [F,Z,K,B,C,D,T,V,a]
    ring
  rw [← heq] at hpos
  exact nonneg_of_mul_nonneg_right hpos (by positivity : 0 < b^4)

end Cone

namespace Cone

private def birth (n d j : ℕ) : ℚ :=
  (((n:ℚ)+j)*((d:ℚ)-j))^3

private def death (n d j : ℕ) : ℚ :=
  ((j:ℚ)*((n:ℚ)+d-j))^3

private theorem rise (p j : ℕ) :
    ((p:ℚ)+j+1) * (Nat.choose (p+j) j : ℚ) =
    (Nat.choose (p+(j+1)) (j+1) : ℚ) * (j+1) := by
  have h := Nat.add_one_mul_choose_eq (p+j) j
  rw [Nat.add_assoc] at h
  exact_mod_cast h

private theorem balance (p d j : ℕ) (hj : j < d) :
    w (p+1) d j * birth (p+1) d j =
    w (p+1) d (j+1) * death (p+1) d (j+1) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d = j+k+1 := ⟨d-j-1, by omega⟩
  subst d
  dsimp only [w,birth,death]
  rw [show j+k+1-j=k+1 by omega, show j+k+1-(j+1)=k by omega]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  rw [← mul_pow, ← mul_pow]
  apply congrArg (fun z : ℚ => z^3)
  calc
    _ = (((p:ℚ)+j+1) * (Nat.choose (p+j) j : ℚ)) *
        ((Nat.choose (p+(k+1)) (k+1) : ℚ) * (k+1)) := by ring
    _ = ((Nat.choose (p+(j+1)) (j+1) : ℚ) * (j+1)) *
        (((p:ℚ)+k+1) * (Nat.choose (p+k) k : ℚ)) := by rw [rise p j, rise p k]
    _ = _ := by ring

theorem cancellation (n d : ℕ) (hn : 0<n) :
    ∑ j ∈ Finset.range (d+1), w n d j * Z n ((d:ℚ)/2) ((xval d j)^2) = 0 := by
  obtain ⟨p,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let n := p+1
  change ∑ j ∈ Finset.range (d+1), w n d j * Z n ((d:ℚ)/2) ((xval d j)^2) = 0
  let L (j : ℕ) := w n d j * birth n d j * (xval d j+1/2)
  let M (j : ℕ) := w n d j * death n d j * (xval d j-1/2)
  have hz (j : ℕ) : w n d j * Z n ((d:ℚ)/2) ((xval d j)^2) = M j - L j := by
    dsimp only [M,L,Z,death,birth,xval]
    ring
  have he (j : ℕ) (hj : j<d) : M (j+1) = L j := by
    dsimp only [M,L]
    rw [← balance p d j hj]
    congr 1
    simp only [xval, Nat.cast_add, Nat.cast_one]
    ring
  have hm : M 0=0 := by simp [M,death]
  have hl : L d=0 := by simp [L,birth]
  simp only [hz, Finset.sum_sub_distrib]
  rw [Finset.sum_range_succ' M, Finset.sum_range_succ L, hm, hl, add_zero, add_zero]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro j hj
  exact he j (Finset.mem_range.mp hj)

end Cone

namespace Cone

theorem weighted_nonneg (n d : ℕ) (hd : 0 < d) (hl : d ≤ n) (hu : n ≤ 3*d) :
    0 ≤ ∑ j ∈ Finset.range (d+1), w n d j * F n ((d:ℚ)/2) ((xval d j)^2) := by
  let b := (d:ℚ)/2
  have hb : 0 < b := by dsimp [b]; positivity
  have hlow : 2*b ≤ n := by
    dsimp [b]
    have h : (d:ℚ) ≤ n := by exact_mod_cast hl
    linarith
  have hhigh : (n:ℚ) ≤ 6*b := by
    dsimp [b]
    have h : (n:ℚ) ≤ 3*(d:ℚ) := by exact_mod_cast hu
    linarith
  have ht : 0 ≤ ∑ j ∈ Finset.range (d+1),
      w n d j * (b^2 * F n b ((xval d j)^2) - K n b * Z n b ((xval d j)^2)) := by
    apply Finset.sum_nonneg
    intro j hj
    have hj' : j ≤ d := by have := Finset.mem_range.mp hj; omega
    have hjq : (j:ℚ) ≤ d := by exact_mod_cast hj'
    have hs : (xval d j)^2 ≤ b^2 := by
      dsimp only [xval,b]
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℚ) j) (sub_nonneg.mpr hjq)]
    have hw : 0 ≤ w n d j := by dsimp only [w]; positivity
    exact mul_nonneg hw (pointwise n b _ hb hlow hhigh (sq_nonneg _) hs)
  have he (j : ℕ) : w n d j * (b^2 * F n b ((xval d j)^2) - K n b * Z n b ((xval d j)^2)) =
      b^2*(w n d j * F n b ((xval d j)^2)) - K n b*(w n d j * Z n b ((xval d j)^2)) := by ring
  simp only [he, Finset.sum_sub_distrib, ← Finset.mul_sum] at ht
  have hz : ∑ j ∈ Finset.range (d+1), w n d j * Z n b ((xval d j)^2) = 0 :=
    cancellation n d (by omega)
  rw [hz, mul_zero, sub_zero] at ht
  exact nonneg_of_mul_nonneg_right ht (sq_pos_of_pos hb)

end Cone

namespace Cone
open Finset

private def bq (n j : ℕ) : ℚ := Nat.choose (n+j) j

private theorem bq_succ (n j : ℕ) :
    bq (n+1) j = bq n j * ((n:ℚ)+j+1)/(n+1) := by
  have h := Nat.choose_mul_succ_eq (n+j) j
  rw [show n+j+1-j = n+1 by omega, show n+j+1 = n+1+j by omega] at h
  have hc := congrArg (fun z : ℕ => (z : ℚ)) h
  change ((Nat.choose (n+j) j * (n+1+j) : ℕ) : ℚ) =
    ((Nat.choose (n+1+j) j * (n+1) : ℕ) : ℚ) at hc
  push_cast at hc
  apply (eq_div_iff (by positivity : (n:ℚ)+1 ≠ 0)).2
  unfold bq
  linarith only [hc]

private theorem bq_prev (n j : ℕ) (hn : 1 ≤ n) :
    bq n j = bq (n-1) j * ((n:ℚ)+j)/n := by
  cases n with
  | zero => omega
  | succ k =>
    rw [show k.succ - 1 = k by omega, bq_succ k j]
    push_cast
    ring

private def termF (n j r : ℚ) : ℚ :=
  n^3*((n+r)*(n+r+1))^3 - (n+1)^3*((n+j)*(n+r))^3

private def raw (n d j : ℕ) : ℚ :=
  w n d j * termF n j ((d-j : ℕ) : ℚ)

private theorem entryQ (n j : ℕ) (hj : j ≤ n) :
    ((SunCubic.entry 3 n j : ℤ) : ℚ) = bq n j ^ 3 := by
  simp [SunCubic.entry, hj, bq]

private theorem scaledSum (n d : ℕ) (h : d+1 ≤ n) :
    (n:ℚ)^6*(n+1)^3*(SunCubic.delta 3 n d : ℚ) =
      ∑ j ∈ range (d+1), raw n d j := by
  have hn : 1 ≤ n := by omega
  have hn0 : (n:ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hs : (n:ℚ)+1 ≠ 0 := by positivity
  simp only [SunCubic.delta, SunCubic.prodCoeff, Int.cast_sub, Int.cast_sum, Int.cast_mul]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [entryQ (n-1) j (by omega), entryQ (n+1) (d-j) (by omega),
      entryQ n j (by omega), entryQ n (d-j) (by omega)]
  rw [bq_succ n (d-j), bq_prev n (d-j) hn, bq_prev n j hn]
  unfold raw w termF bq
  field_simp

set_option maxHeartbeats 2000000 in
theorem coefficientIdentity (n d : ℕ) (h : d+1 ≤ n) :
    (n:ℚ)^6*(n+1)^3*(SunCubic.delta 3 n d : ℚ) =
      ∑ j ∈ range (d+1), w n d j * F n ((d:ℚ)/2) ((xval d j)^2) := by
  rw [scaledSum n d h]
  have reflectSum : (∑ j ∈ range (d+1), raw n d (d-j)) =
      ∑ j ∈ range (d+1), raw n d j := by
    simpa using Finset.sum_range_reflect (raw n d) (d+1)
  calc
    _ = ((∑ j ∈ range (d+1), raw n d j) + ∑ j ∈ range (d+1), raw n d (d-j)) / 2 := by
      rw [reflectSum]; ring
    _ = _ := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      have hd : j ≤ d := by have := Finset.mem_range.mp hj; omega
      have hd' : d-(d-j) = j := by omega
      have hs : w n d (d-j) = w n d j := by
        unfold w
        rw [hd', mul_comm]
      unfold raw
      rw [hs, hd', Nat.cast_sub hd]
      unfold F xval termF
      ring

end Cone

namespace SunCubic

theorem middleConePolynomial (n d : ℕ) (hd : d<n) (hu : n≤3*d) :
    0 ≤ (R 3 (n-1) * R 3 (n+1) - (R 3 n)^2).coeff d := by
  rw [coeffDelta]
  have h := Cone.weighted_nonneg n d (by omega) (by omega) hu
  rw [← Cone.coefficientIdentity n d (by omega)] at h
  have hn : 0 < (n:ℚ) := by exact_mod_cast (show 0<n by omega)
  have hq : (0:ℚ) ≤ (delta 3 n d : ℚ) :=
    nonneg_of_mul_nonneg_right h (by positivity : 0 < (n:ℚ)^6*(n+1)^3)
  exact_mod_cast hq


end SunCubic

namespace Cone
open Finset

private theorem scaledTerm (n j r : ℕ) (hn : 0 < n) :
    (n:ℚ)^6*(n+1)^3 *
      ((bq (n-1) j)^3*(bq (n+1) r)^3 - (bq n j)^3*(bq n r)^3) =
    (bq (n-1) j * bq (n-1) r)^3 * termF n j r := by
  have hn0 : (n:ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [bq_succ n r, bq_prev n r hn, bq_prev n j hn]
  unfold termF
  field_simp

private theorem scaledSumDiag (n : ℕ) (hn : 0<n) :
    (n:ℚ)^6*(n+1)^3*(SunCubic.delta 3 n n : ℚ) +
        (n:ℚ)^6*(n+1)^3 * w n n n =
    ∑ j ∈ range (n+1), raw n n j := by
  let c (j : ℕ) : ℚ := (n:ℚ)^6*(n+1)^3 *
    (((SunCubic.entry 3 (n-1) j : ℤ) : ℚ) * (SunCubic.entry 3 (n+1) (n-j) : ℚ) -
     ((SunCubic.entry 3 n j : ℤ) : ℚ) * (SunCubic.entry 3 n (n-j) : ℚ))
  have main : ∑ j ∈ range n, c j = ∑ j ∈ range n, raw n n j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    dsimp only [c]
    rw [entryQ (n-1) j (by omega), entryQ (n+1) (n-j) (by omega),
        entryQ n j (by omega), entryQ n (n-j) (by omega)]
    exact scaledTerm n j (n-j) hn
  have last : c n + (n:ℚ)^6*(n+1)^3 * w n n n = raw n n n := by
    calc
      _ = (n:ℚ)^6*(n+1)^3 *
          ((bq (n-1) n)^3*(bq (n+1) 0)^3 - (bq n n)^3*(bq n 0)^3) := by
        simp [c, w, bq, SunCubic.entry, show ¬ n ≤ n-1 by omega]
        ring
      _ = _ := by simpa only [raw,w,bq,Nat.sub_self] using scaledTerm n n 0 hn
  simp only [SunCubic.delta, SunCubic.prodCoeff, Int.cast_sub, Int.cast_sum, Int.cast_mul]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  change (∑ j ∈ range (n+1), c j) + _ = _
  rw [Finset.sum_range_succ c, Finset.sum_range_succ (raw n n), main, add_assoc, last]

set_option maxHeartbeats 2000000 in
theorem diagonalIdentity (n : ℕ) (hn : 0<n) :
    (n:ℚ)^6*(n+1)^3*(SunCubic.delta 3 n n : ℚ) +
        (n:ℚ)^6*(n+1)^3 * w n n n =
    ∑ j ∈ range (n+1), w n n j * F n ((n:ℚ)/2) ((xval n j)^2) := by
  rw [scaledSumDiag n hn]
  have reflectDiag : (∑ j ∈ range (n+1), raw n n (n-j)) =
      ∑ j ∈ range (n+1), raw n n j := by
    simpa using Finset.sum_range_reflect (raw n n) (n+1)
  calc
    _ = ((∑ j ∈ range (n+1), raw n n j) + ∑ j ∈ range (n+1), raw n n (n-j)) / 2 := by
      rw [reflectDiag]; ring
    _ = _ := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≤ n := by have := Finset.mem_range.mp hj; omega
      have hmirror : n-(n-j) = j := by omega
      have hs : w n n (n-j) = w n n j := by unfold w; rw [hmirror, mul_comm]
      unfold raw
      rw [hs, hmirror, Nat.cast_sub hj']
      unfold F xval termF
      ring

end Cone

namespace Cone

set_option maxHeartbeats 1000000 in
theorem weighted_diag (n : ℕ) (hn : 0<n) :
    (n:ℚ)^6*(n+1)^3*w n n n ≤
      ∑ j ∈ Finset.range (n+1), w n n j * F n ((n:ℚ)/2) ((xval n j)^2) := by
  let b := (n:ℚ)/2
  let G (j : ℕ) := w n n j * (b^2 * F n b ((xval n j)^2) - K n b * Z n b ((xval n j)^2))
  have hb : 0 < b := by dsimp [b]; positivity
  have hw (j : ℕ) : 0 ≤ w n n j := by dsimp only [w]; positivity
  have hg (j : ℕ) (hj : j ≤ n) : 0 ≤ G j := by
    have hq : (j:ℚ) ≤ n := by exact_mod_cast hj
    have hs : (xval n j)^2 ≤ b^2 := by
      dsimp only [xval,b]
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℚ) j) (sub_nonneg.mpr hq)]
    exact mul_nonneg (hw j) (pointwise n b _ hb (by dsimp [b]; linarith)
      (by dsimp [b]; linarith [Nat.cast_nonneg (α := ℚ) n]) (sq_nonneg _) hs)
  have hedge : b^2*(n:ℚ)^6*(n+1)^3 ≤ b^2*F n b ((xval n n)^2)-K n b*Z n b ((xval n n)^2) := by
    have hid : b^2*F n b ((xval n n)^2)-K n b*Z n b ((xval n n)^2) -
        b^2*(n:ℚ)^6*(n+1)^3 = (n:ℚ)^8/8*(20*(n:ℚ)^3+27*(n:ℚ)^2+23*(n:ℚ)+10) := by
      dsimp only [b,xval,F,Z,K]
      ring
    have hp : (0:ℚ) ≤ (n:ℚ)^8/8*(20*(n:ℚ)^3+27*(n:ℚ)^2+23*(n:ℚ)+10) := by positivity
    linarith
  have ht : b^2*((n:ℚ)^6*(n+1)^3*w n n n) ≤ ∑ j ∈ Finset.range (n+1), G j := by
    rw [Finset.sum_range_succ]
    have hprev : 0 ≤ ∑ j ∈ Finset.range n, G j :=
      Finset.sum_nonneg fun i hi => hg i (Nat.le_of_lt (Finset.mem_range.mp hi))
    have hp := mul_le_mul_of_nonneg_left hedge (hw n)
    dsimp only [G]
    calc
      _ = w n n n * (b^2*(n:ℚ)^6*(n+1)^3) := by ring
      _ ≤ _ := le_trans hp (le_add_of_nonneg_left hprev)
  have he (j : ℕ) : G j =
      b^2*(w n n j * F n b ((xval n j)^2)) - K n b*(w n n j * Z n b ((xval n j)^2)) := by
    dsimp only [G]
    ring
  simp only [he, Finset.sum_sub_distrib, ← Finset.mul_sum] at ht
  have hz : ∑ j ∈ Finset.range (n+1), w n n j * Z n b ((xval n j)^2) = 0 := cancellation n n hn
  rw [hz, mul_zero, sub_zero] at ht
  apply le_of_not_gt
  intro hbad
  exact (not_lt_of_ge ht) (mul_lt_mul_of_pos_left hbad (sq_pos_of_pos hb))

end Cone

namespace Cone

theorem diagonalNonneg (n : ℕ) (hn : 0 < n) : 0 ≤ SunCubic.delta 3 n n := by
  have bound := weighted_diag n hn
  rw [← diagonalIdentity n hn] at bound
  have hpos : 0 < (n:ℚ)^6 * (n+1)^3 := by positivity
  have hmul : 0 ≤ (n:ℚ)^6 * (n+1)^3 * (SunCubic.delta 3 n n : ℚ) := by linarith only [bound]
  have hrat := nonneg_of_mul_nonneg_right hmul hpos
  exact_mod_cast hrat

end Cone

namespace Cone

theorem flux_algebra (A B t : ℚ) (hA : 0 ≤ A) (hB : 3*A ≤ B)
    (hdisc : t=0 ∨ 1 ≤ t^2) :
    ((B+t)^3*(A-t) - (B-t)^3*(A+t)) * ((t/2)^3-(t/2)/4) ≤ 0 := by
  rcases hdisc with ht | ht
  · simp [ht]
  · have h1 : 0 ≤ B - 3*A := by linarith
    have h2 : 0 ≤ 3*B - A := by linarith
    have h3 : 0 ≤ t^2 - 1 := by linarith
    have hid : ((B+t)^3*(A-t) - (B-t)^3*(A+t)) * ((t/2)^3-(t/2)/4) =
        -(t^2*(t^2-1)*(B^2*(B-3*A)+t^2*(3*B-A)))/4 := by ring
    rw [hid]
    have hp : 0 ≤ t^2*(t^2-1)*(B^2*(B-3*A)+t^2*(3*B-A)) := by positivity
    linarith

end Cone

namespace Cone

private def rb (n b : ℚ) : ℚ :=
  let a := n+b
  let T := a*(a+1)
  let V := 2*a+1
  b^2*(3*n^3*T^2+3*n^3*V^2*T+3*(n+1)^3*a^4) -
    K n b*((6*n+3)*(a*b)^2-3*n^2*a*b)

private def rc (n b : ℚ) : ℚ :=
  let a := n+b
  let T := a*(a+1)
  let V := 2*a+1
  b^2*(3*n^3*(T+V^2)-3*(n+1)^3*a^2) -
    K n b*(-12*n*a*b+2*n^3-3*a*b+3*n^2)

private def rd (n b : ℚ) : ℚ := b^2*(n^3+(n+1)^3)-K n b*(6*n+1)

set_option maxHeartbeats 5000000 in
private theorem large_signs (n b : ℚ) (hb : 1 ≤ b) (hn : 6*b ≤ n) :
    0 ≤ rb n b ∧ rd n b ≤ 0 ∧ 0 ≤ rb n b + b*rc n b + b^3*rd n b := by
  let u := n-6*b
  let v := b-1
  have hU : 0 ≤ u := sub_nonneg.mpr hn
  have hV : 0 ≤ v := sub_nonneg.mpr hb
  have hb' : b = 1+v := by dsimp [v]; ring
  have hn' : n = 6*(1+v)+u := by dsimp [u,v]; ring
  refine ⟨?_,?_,?_⟩
  · dsimp only [rb,K]
    rw [hn',hb']
    ring_nf
    positivity
  · apply neg_nonneg.mp
    dsimp only [rd,K]
    rw [hn',hb']
    ring_nf
    positivity
  · dsimp only [rb,rc,rd,K]
    rw [hn',hb']
    ring_nf
    positivity

theorem largeWeighted (n d : ℕ) (hd : 2 ≤ d) (hn : 3*d ≤ n)
    (hmoment : (∑ j ∈ Finset.range (d+1), w n d j * ((xval d j)^2)^2) ≤
     ((d:ℚ)/2) * ∑ j ∈ Finset.range (d+1), w n d j * (xval d j)^2) :
    0 ≤ ∑ j ∈ Finset.range (d+1), w n d j * F n ((d:ℚ)/2) ((xval d j)^2) := by
  let b := (d:ℚ)/2
  let s (j : ℕ) := (xval d j)^2
  let B := rb n b
  let C := rc n b
  let D := rd n b
  let M1 := ∑ j ∈ Finset.range (d+1), w n d j * s j
  let M2 := ∑ j ∈ Finset.range (d+1), w n d j * (s j)^2
  let M3 := ∑ j ∈ Finset.range (d+1), w n d j * (s j)^3
  have hb : 1 ≤ b := by
    dsimp [b]
    have h : (2:ℚ) ≤ d := by exact_mod_cast hd
    linarith
  have hnb : 6*b ≤ (n:ℚ) := by
    dsimp [b]
    have h : 3*(d:ℚ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨hB,hD,hT⟩ := large_signs n b hb hnb
  change 0 ≤ B at hB
  change D ≤ 0 at hD
  change 0 ≤ B+b*C+b^3*D at hT
  have hw (j : ℕ) : 0 ≤ w n d j := by dsimp only [w]; positivity
  have hM1 : 0 ≤ M1 := Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (sq_nonneg _)
  have hM2 : 0 ≤ M2 := Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (sq_nonneg _)
  have h21 : M2 ≤ b*M1 := hmoment
  have h32 : M3 ≤ b^2*M2 := by
    dsimp only [M3,M2]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hj' : j ≤ d := by have := Finset.mem_range.mp hj; omega
    have hjq : (j:ℚ) ≤ d := by exact_mod_cast hj'
    have hs : s j ≤ b^2 := by
      dsimp only [s,xval,b]
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℚ) j) (sub_nonneg.mpr hjq)]
    calc
      _ = s j * (w n d j * (s j)^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hs (mul_nonneg (hw j) (sq_nonneg _))
  have hh : 0 ≤ B*M1+C*M2+D*M3 := by
    have h3 := mul_le_mul_of_nonpos_left h32 hD
    by_cases hq : 0 ≤ C+D*b^2
    · nlinarith [mul_nonneg hB hM1, mul_nonneg hq hM2]
    · have h2 := mul_le_mul_of_nonpos_left h21 (le_of_not_ge hq)
      nlinarith [mul_nonneg hT hM1]
  have he (j : ℕ) : b^2*(w n d j * F n b (s j))-K n b*(w n d j * Z n b (s j)) =
      B*(w n d j * s j) + C*(w n d j * (s j)^2) + D*(w n d j * (s j)^3) := by
    dsimp only [B,C,D,rb,rc,rd,F,Z,K]
    ring
  have hid : (∑ j ∈ Finset.range (d+1), _) = (∑ j ∈ Finset.range (d+1), _) :=
    Finset.sum_congr rfl (fun j _ => he j)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hid
  have hz : ∑ j ∈ Finset.range (d+1), w n d j * Z n b (s j) = 0 :=
    cancellation n d (by omega)
  rw [hz,mul_zero,sub_zero] at hid
  change b^2*(∑ j ∈ Finset.range (d+1), w n d j * F n b (s j)) = B*M1+C*M2+D*M3 at hid
  rw [← hid] at hh
  have hb' : 0 < b := lt_of_lt_of_le zero_lt_one hb
  exact nonneg_of_mul_nonneg_right hh (sq_pos_of_pos hb')

end Cone


namespace Cone

theorem edgeSign (n d j : ℕ) (hd : 2 ≤ d) (hn : 3*d ≤ n) (hj : j<d) :
    (w n d (j+1) * ((j:ℚ)+1)^2 - w n d j * ((d:ℚ) - (j:ℚ))^2) *
      ((xval d j+1/2)^3 - (xval d j+1/2)/4) ≤ 0 := by
  let A := (d:ℚ)+1
  let B := 2*(n:ℚ)+d-1
  let t := 2*(j:ℚ)+1-d
  let I := (j:ℚ)+1
  let J := (d:ℚ)-j
  let P := (n:ℚ)+j
  let Q := (n:ℚ)+d-j-1
  have hnq : (3:ℚ)*d ≤ n := by exact_mod_cast hn
  have hdq : (2:ℚ) ≤ d := by exact_mod_cast hd
  have hjq : (j:ℚ)+1 ≤ d := by exact_mod_cast (show j+1 ≤ d by omega)
  have ha : 0 ≤ A := by dsimp [A]; linarith
  have hb : 3*A ≤ B := by dsimp [A,B]; linarith
  have ht : t=0 ∨ 1≤t^2 := by
    rcases lt_trichotomy (2*j+1) d with h | h | h
    · have hq : (2:ℚ)*j+1+1 ≤ d := by exact_mod_cast (show 2*j+1+1 ≤ d by omega)
      right
      dsimp [t]
      nlinarith [sq_nonneg ((2:ℚ)*j+1-d+1)]
    · have hq : (2:ℚ)*j+1 = d := by exact_mod_cast h
      left
      dsimp [t]
      linarith
    · have hq : (d:ℚ)+1 ≤ 2*j+1 := by exact_mod_cast (show d+1 ≤ 2*j+1 by omega)
      right
      dsimp [t]
      nlinarith [sq_nonneg ((2:ℚ)*j+1-d-1)]
  have hsmall : (P^3*J-Q^3*I)*((xval d j+1/2)^3-(xval d j+1/2)/4) ≤ 0 := by
    have hs := flux_algebra A B t ha hb ht
    have he : (P^3*J-Q^3*I)*((xval d j+1/2)^3-(xval d j+1/2)/4) =
        (((B+t)^3*(A-t) - (B-t)^3*(A+t)) * ((t/2)^3-(t/2)/4))/16 := by
      dsimp only [P,J,Q,I,A,B,t,xval]
      ring
    rw [he]
    exact div_nonpos_of_nonpos_of_nonneg hs (by norm_num)
  have bal : w n d j*(P*J)^3=w n d (j+1)*(I*Q)^3 := by
    dsimp only [P,J,Q,I]
    obtain ⟨p,rfl⟩ : ∃ p : ℕ, n=p+1 := ⟨n-1,by omega⟩
    have h := balance p d j hj
    dsimp only [birth,death] at h
    push_cast at h ⊢
    convert h using 1
    ring
  have hnon : 0 ≤ w n d j * J^2 := by unfold w; positivity
  have hi : 0<I := by dsimp [I]; positivity
  have hq : 0<Q := by dsimp [Q]; linarith
  let y := xval d j+1/2
  have eqn : (w n d (j+1)*I^2-w n d j*J^2) *(y^3-y/4)*(I*Q^3) =
      (w n d j*J^2) * ((P^3*J-Q^3*I)*(y^3-y/4)) := by
    linear_combination -(y^3-y/4)*bal
  change (w n d (j+1)*I^2-w n d j*J^2)*(y^3-y/4) ≤ 0
  by_contra! h
  have pos := mul_pos h (mul_pos hi (pow_pos hq 3))
  rw [eqn] at pos
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hnon hsmall)) pos

end Cone

namespace Cone

private def psiMoment (y : ℚ) : ℚ := y^3-y/4

theorem moment_bound (n d : ℕ) (hd : 2 ≤ d) (hn : 3*d ≤ n) :
    ∑ j ∈ Finset.range (d+1), w n d j * ((xval d j)^2)^2 ≤
    ((d:ℚ)/2) * ∑ j ∈ Finset.range (d+1), w n d j * (xval d j)^2 := by
  let b : ℚ := (d:ℚ)/2
  let s (j : ℕ) : ℚ := (xval d j)^2
  let T := Finset.range (d+1)
  let A := ∑ j ∈ T, w n d j * (s j)^2
  let B := ∑ j ∈ T, w n d j * s j
  let L (j : ℕ) := w n d j * ((d:ℚ)-j)^2 * psiMoment (xval d j + 1/2)
  let M (j : ℕ) := w n d j * (j:ℚ)^2 * psiMoment (xval d j - 1/2)
  have he (j : ℕ) (hj : j<d) : M (j+1) ≤ L j := by
    have hr : xval d (j+1) - 1/2 = xval d j + 1/2 := by
      unfold xval
      push_cast
      ring
    dsimp only [M,L]
    rw [hr, Nat.cast_add, Nat.cast_one]
    exact sub_nonpos.mp (by simpa only [psiMoment,sub_mul] using edgeSign n d j hd hn hj)
  have hm : M 0=0 := by simp [M]
  have hl : L d=0 := by simp [L]
  have ht : ∑ j ∈ T, M j ≤ ∑ j ∈ T, L j := by
    dsimp only [T]
    rw [Finset.sum_range_succ' M, Finset.sum_range_succ L, hm, hl, add_zero, add_zero]
    exact Finset.sum_le_sum fun j hj => he j (Finset.mem_range.mp hj)
  have hid (j : ℕ) : M j-L j =
      (4*b-3)*(w n d j*(s j)^2) - (3*b^2-2*b)*(w n d j*s j) := by
    dsimp only [M,L,psiMoment,b,s,xval]
    ring
  have hz : (4*b-3)*A ≤ (3*b^2-2*b)*B := by
    apply sub_nonpos.mp
    have hsum := sub_nonpos.mpr ht
    rw [← Finset.sum_sub_distrib] at hsum
    simp only [hid,Finset.sum_sub_distrib,← Finset.mul_sum] at hsum
    exact hsum
  have hb : 1 ≤ b := by
    have : (2:ℚ) ≤ d := by exact_mod_cast hd
    dsimp [b]
    linarith
  have hB : 0 ≤ B := by
    dsimp only [B]
    apply Finset.sum_nonneg
    intro j hj
    dsimp [w,s]
    positivity
  have hh : (3*b^2-2*b)*B ≤ (4*b-3)*(b*B) := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : 0 ≤ b) (by linarith : 0 ≤ b-1)) hB]
  exact le_of_mul_le_mul_left (hz.trans hh) (by linarith : 0 < 4*b-3)

end Cone

namespace SunCubic
theorem middleClosedPolynomial (n d : ℕ) (hn : 0 < n) (hd : d ≤ n) (hu : n ≤ 3*d) :
    0 ≤ (R 3 (n-1) * R 3 (n+1) - (R 3 n)^2).coeff d := by
  rcases lt_or_eq_of_le hd with h | rfl
  · exact middleConePolynomial n d h hu
  · rw [coeffDelta]
    exact Cone.diagonalNonneg _ hn

theorem lowerHalf (n d : ℕ) (hn : 0 < n) (hd : d ≤ n) :
    0 ≤ (R 3 (n-1) * R 3 (n+1) - (R 3 n)^2).coeff d := by
  by_cases hsmall : d ≤ 2
  · exact lowDegrees n d hn hsmall
  by_cases hm : n ≤ 3*d
  · exact middleClosedPolynomial n d hn hd hm
  have ha := Cone.largeWeighted n d (by omega) (by omega) (Cone.moment_bound n d (by omega) (by omega))
  rw [← Cone.coefficientIdentity n d (by omega)] at ha
  have hnat : (0:ℚ) < n := by exact_mod_cast hn
  have hp : (0:ℚ) ≤ (delta 3 n d : ℚ) :=
    nonneg_of_mul_nonneg_right ha (by positivity : 0 < (n:ℚ)^6*(n+1)^3)
  rw [coeffDelta]
  exact_mod_cast hp
end SunCubic
namespace Cone

/-- On the truncated interval l..n the Stein sum is exactly the two endpoint fluxes. -/
theorem truncatedStein (n l : ℕ) (hn : 0<n) (hl : l≤n) (g : ℕ → ℚ) :
    (∑ i ∈ Finset.range (n-l+1), w n (n+l) (l+i) *
      (death n (n+l) (l+i) * g (l+i) - birth n (n+l) (l+i) * g (l+i+1))) =
    w n (n+l) l * death n (n+l) l * g l -
    w n (n+l) n * birth n (n+l) n * g (n+1) := by
  obtain ⟨p,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let n := p+1
  let d := n+l
  let A (i : ℕ) := w n d (l+i) * birth n d (l+i) * g (l+i+1)
  let M (i : ℕ) := w n d (l+i) * death n d (l+i) * g (l+i)
  have hz (i : ℕ) : w n d (l+i) * (death n d (l+i)*g (l+i) -
      birth n d (l+i)*g (l+i+1)) = M i - A i := by dsimp only [M,A]; ring
  have he (i : ℕ) (hi : i < n-l) : M (i+1) = A i := by
    dsimp only [M,A]
    rw [← Nat.add_assoc l i 1, ← balance p d (l+i) (by dsimp [d,n] at *; omega)]
  have hsum : ∑ i ∈ Finset.range (n-l), M (i+1) = ∑ i ∈ Finset.range (n-l), A i :=
    Finset.sum_congr rfl fun i hi => he i (Finset.mem_range.mp hi)
  trans ∑ i ∈ Finset.range (n-l+1), (M i-A i)
  · exact Finset.sum_congr rfl (fun i _ => hz i)
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_range_succ' M, Finset.sum_range_succ A, hsum]
  have hl' : l+(n-l)=n := by dsimp [n]; omega
  have hbase : M 0 = w n d l * death n d l * g l := by simp [M]
  have hend : A (n-l) = w n d n * birth n d n * g (n+1) := by
    dsimp only [A]
    rw [hl']
  rw [hbase,hend]
  ring

def Eflux (n l : ℕ) : ℚ := (2*(n:ℚ)*l)^3

theorem truncatedCancel (n l : ℕ) (hn : 0<n) (hl : l≤n) :
    (∑ i ∈ Finset.range (n-l+1), w n (n+l) (l+i) * Z n (((n:ℚ)+l)/2) ((xval (n+l) (l+i))^2)) =
      -w n (n+l) n * Eflux n l * ((n:ℚ)-l+1) := by
  let d := n+l
  let g (j : ℕ) := xval d j - 1/2
  have ht := truncatedStein n l hn hl g
  have hterm (j : ℕ) : death n d j * g j - birth n d j * g (j+1) =
      Z n (((n:ℚ)+l)/2) ((xval d j)^2) := by
    dsimp [d,g,Z,death,birth,xval]
    push_cast
    ring
  change (∑ i ∈ Finset.range (n-l+1), w n d (l+i) * (death n d (l+i)*g (l+i) -
    birth n d (l+i)*g (l+i+1))) = _ at ht
  simp only [hterm] at ht
  rw [ht]
  have hw : w n d l = w n d n := by simp [w,d, Nat.add_sub_cancel_left, mul_comm]
  rw [hw]
  dsimp [death,birth,g,xval,d,Eflux]
  push_cast
  ring

end Cone

namespace Cone

def psiF (y : ℚ) : ℚ := y^3-y/4

def ZF (b s : ℚ) : ℚ := (3*b^2-3*b^3)*s+(6*b^2-9*b+1)*s^2+2*s^3

private theorem franelEdge (n d j : ℕ) (hn : 0<n) (hj : j<d) :
    0 ≤ (w n d (j+1)*((j:ℚ)+1)^3 - w n d j*((d:ℚ)-j)^3)*psiF (xval d j+1/2) := by
  let y := xval d j + 1/2
  let I := (j:ℚ)+1
  let J := (d:ℚ)-j
  let P := (n:ℚ)+j
  let Q := (n:ℚ)+d-j-1
  have hjq : (j:ℚ)+1 ≤ d := by exact_mod_cast (show j+1≤d by omega)
  have hnq : (1:ℚ) ≤ n := by exact_mod_cast (show 1≤n by omega)
  have hp : 0 ≤ P := by dsimp [P]; positivity
  have hq : 0 < Q := by dsimp [Q]; linarith
  have hjj : 0 ≤ J := by dsimp [J]; linarith
  have hy : y=0 ∨ 1/4 ≤ y^2 := by
    rcases lt_trichotomy (2*j+1) d with h|h|h
    · have HH : 2*(j:ℚ)+1+1 ≤ d := by exact_mod_cast (show 2*j+1+1≤d by omega)
      right
      dsimp [y,xval]
      nlinarith [sq_nonneg ((j:ℚ)-(d:ℚ)/2+1)]
    · have HH : 2*(j:ℚ)+1 = d := by exact_mod_cast h
      left
      dsimp [y,xval]
      linarith
    · have HH : (d:ℚ)+1 ≤ 2*j+1 := by exact_mod_cast (show d+1≤2*j+1 by omega)
      right
      dsimp [y,xval]
      nlinarith [sq_nonneg ((j:ℚ)-(d:ℚ)/2)]
  have hsmall : 0 ≤ (P^3-Q^3)*psiF y := by
    have he : (P^3-Q^3)*psiF y = 2*y^2*(y^2-1/4)*(P^2+P*Q+Q^2) := by
      dsimp only [P,Q,y,xval,psiF]
      ring
    rw [he]
    rcases hy with hy|hy
    · rw [hy]; norm_num
    · have hs : 0 ≤ y^2-1/4 := sub_nonneg.mpr hy
      positivity
  have hbal : w n d j*(P*J)^3=w n d (j+1)*(I*Q)^3 := by
    dsimp only [P,J,Q,I]
    obtain ⟨p,rfl⟩ : ∃ p : ℕ, n=p+1 := ⟨n-1,by omega⟩
    have h := balance p d j hj
    dsimp only [birth,death] at h
    push_cast at h ⊢
    convert h using 1 <;> ring
  have heq : Q^3*((w n d (j+1)*I^3-w n d j*J^3)*psiF y) =
      (w n d j * J^3)*((P^3-Q^3)*psiF y) := by
    linear_combination -(psiF y)*hbal
  have hw : 0 ≤ w n d j := by dsimp [w]; positivity
  have hh := mul_nonneg (mul_nonneg hw (pow_nonneg hjj 3)) hsmall
  rw [← heq] at hh
  exact nonneg_of_mul_nonneg_right hh (pow_pos hq 3)

theorem truncatedFranel (n l : ℕ) (hn : 0<n) (hl : l≤n) :
    -2*w n (n+l) n*(l:ℚ)^3*psiF (((n:ℚ)-l+1)/2) ≤
    ∑ i ∈ Finset.range (n-l+1), w n (n+l) (l+i) * ZF (((n:ℚ)+l)/2) ((xval (n+l) (l+i))^2) := by
  let d := n+l
  let M (i : ℕ) := w n d (l+i) * ((l:ℚ)+i)^3 * psiF (xval d (l+i)-1/2)
  let A (i : ℕ) := w n d (l+i) * ((d:ℚ)-(l+i))^3 * psiF (xval d (l+i)+1/2)
  have hz (i : ℕ) : w n d (l+i) * ZF (((n:ℚ)+l)/2) ((xval d (l+i))^2) = M i-A i := by
    dsimp [M,A,d,ZF,xval,psiF]
    push_cast
    ring
  have he (i : ℕ) (hi : i<n-l) : A i ≤ M (i+1) := by
    have h := franelEdge n d (l+i) hn (by dsimp [d]; omega)
    have hy : xval d (l+(i+1))-1/2 = xval d (l+i)+1/2 := by dsimp [xval]; push_cast; ring
    dsimp only [M,A]
    rw [hy]
    rw [Nat.add_assoc l i 1] at h
    push_cast at h ⊢
    apply sub_nonneg.mp
    convert h using 1 <;> ring
  have hs := Finset.sum_le_sum (s := Finset.range (n-l)) (fun i hi => he i (Finset.mem_range.mp hi))
  apply le_trans (b := ∑ i ∈ Finset.range (n-l+1), (M i-A i))
  swap
  · exact le_of_eq (Finset.sum_congr rfl (fun i _ => (hz i).symm))
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_range_succ' M, Finset.sum_range_succ A]
  have hEnd : M 0 - A (n-l) = -2*w n d n*(l:ℚ)^3*psiF (((n:ℚ)-l+1)/2) := by
    have hw : w n d l = w n d n := by simp [w,d, Nat.add_sub_cancel_left, mul_comm]
    have hix : l+(n-l)=n := by omega
    dsimp only [M,A]
    simp only [Nat.add_zero, Nat.cast_zero, add_zero, hix, hw]
    dsimp only [d,xval,psiF]
    rw [Nat.cast_sub hl]
    push_cast
    ring
  rw [← hEnd]
  linarith

end Cone

namespace Cone

theorem upperRestrict (f : ℕ → ℚ) (n l : ℕ) (hle : l ≤ n) :
    (∑ j ∈ Finset.range (n+l+1), if l≤j ∧ j≤n then f j else 0) =
      ∑ i ∈ Finset.range (n-l+1), f (l+i) := by
  let g (j : ℕ) : ℚ := if l≤j ∧ j≤n then f j else 0
  change (∑ j ∈ Finset.range (n+l+1), g j) = _
  have ha : (∑ j ∈ Finset.range l, g j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have h := Finset.mem_range.mp hj
    simp [g, show ¬l≤j by omega]
  have hb : (∑ j ∈ Finset.range l, g (n+1+j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [g, show ¬n+1+j≤n by omega]
  rw [show n+l+1 = (n+1)+l by omega, Finset.sum_range_add g (n+1) l, hb, add_zero]
  have hs : (∑ j ∈ Finset.range (n+1), g j) =
      (∑ j ∈ Finset.range l, g j) + ∑ j ∈ Finset.range (n-l+1), g (l+j) := by
    simpa only [show l+(n-l+1)=n+1 by omega] using Finset.sum_range_add g l (n-l+1)
  rw [hs, ha, zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  have h := Finset.mem_range.mp hj
  simp [g, show l≤l+j by omega, show l+j≤n by omega]

end Cone

namespace Cone

private theorem upperSymm (n j : ℕ) : bq n j = bq j n := by
  unfold bq
  rw [show j+n=n+j by omega]
  exact_mod_cast (Nat.choose_symm_add (a:=n) (b:=j)).symm

theorem upperEndGain (n l : ℕ) (hl : 0 < l) (hle : l ≤ n) :
    bq (n-1) (l-1) * bq (n+1) (n+1) =
    (bq (n-1) n * bq (n-1) l) * (4*(2*(n:ℚ)+1)*l/((n+1)*(n+l-1))) := by
  have hn : 1 ≤ n := by omega
  have hnq : (0:ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlq : (0:ℚ) < l := by exact_mod_cast hl
  have hd : (n:ℚ)+l-1 ≠ 0 := by
    have : (1:ℚ) ≤ n := by exact_mod_cast hn
    linarith
  have center : bq (n+1) (n+1) = bq (n-1) n * (4*(2*(n:ℚ)+1)/(n+1)) := by
    rw [bq_succ n (n+1), upperSymm n (n+1), bq_succ n n, bq_prev n n hn]
    push_cast
    field_simp [ne_of_gt hnq] <;> ring
  have tail : bq (n-1) l =
      bq (n-1) (l-1) * ((n:ℚ)+l-1)/l := by
    rw [upperSymm (n-1) l, bq_prev l (n-1) (by omega), upperSymm (l-1) (n-1),
        Nat.cast_sub hn]
    push_cast
    ring
  rw [center,tail]
  field_simp [hd, ne_of_gt hlq] <;> ring

theorem upperEndLoss (n l : ℕ) (hl : 0 < l) (hle : l ≤ n) :
    bq (n-1) n * bq (n+1) l =
    (bq (n-1) n * bq (n-1) l) * (((n:ℚ)+l)*(n+l+1)/(n*(n+1))) := by
  have hn : 1 ≤ n := by omega
  have hnq : (0:ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [bq_succ n l, bq_prev n l hn]
  field_simp [ne_of_gt hnq] <;> ring

end Cone

namespace Cone
open Finset

def upperCorr (n l : ℚ) : ℚ :=
  n^6*(n+1)^3*((4*(2*n+1)*l/((n+1)*(n+l-1)))^3 -
    ((n+l)*(n+l+1)/(n*(n+1)))^3)

private theorem entryAll (a j : ℕ) :
    ((SunCubic.entry 3 a j : ℤ) : ℚ) = if j ≤ a then bq a j^3 else 0 := by
  by_cases h : j ≤ a <;> simp [SunCubic.entry, bq, h]

private theorem symRestricted (n l : ℕ) (hl : l ≤ n) :
    (∑ i ∈ range (n-l+1), raw n (n+l) (l+i)) =
     ∑ i ∈ range (n-l+1), w n (n+l) (l+i) * F n (((n+l:ℕ):ℚ)/2)
         ((xval (n+l) (l+i))^2) := by
  let f (i : ℕ) := raw n (n+l) (l+i)
  have refl : (∑ i ∈ range (n-l+1), f (n-l-i)) =
      ∑ i ∈ range (n-l+1), f i := by
    simpa using Finset.sum_range_reflect f (n-l+1)
  calc
    _ = ((∑ i ∈ range (n-l+1), f i) + ∑ i ∈ range (n-l+1), f (n-l-i))/2 := by
      rw [refl]; change _ = ((∑ i ∈ range (n-l+1), f i) + _)/2; dsimp only [f]; ring
    _ = _ := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have h1 : l+(n-l-i) = n+l-(l+i) := by omega
      have h2 : n+l-(n+l-(l+i)) = l+i := by omega
      have hs : w n (n+l) (n+l-(l+i)) = w n (n+l) (l+i) := by unfold w; rw [h2, mul_comm]
      dsimp only [f,raw]
      rw [h1,hs,h2,Nat.cast_sub (show l+i ≤ n+l by omega)]
      unfold F xval termF
      ring

theorem upperIdentity (n l : ℕ) (hl : 0 < l) (hle : l ≤ n) :
    (n:ℚ)^6*(n+1)^3*(SunCubic.delta 3 n (n+l) : ℚ) =
    (∑ i ∈ range (n-l+1), w n (n+l) (l+i) * F n (((n+l:ℕ):ℚ)/2)
      ((xval (n+l) (l+i))^2)) + w n (n+l) n * upperCorr n l := by
  let S := (n:ℚ)^6*(n+1)^3
  let gain := (bq (n-1) (l-1) * bq (n+1) (n+1))^3
  let loss := (bq (n-1) n * bq (n+1) l)^3
  let u (j : ℕ) := (bq (n-1) j)^3 * (bq (n+1) (n+l-j))^3 -
    (bq n j)^3 * (bq n (n+l-j))^3
  let c (j : ℕ) : ℚ := (SunCubic.entry 3 (n-1) j : ℚ) * (SunCubic.entry 3 (n+1) (n+l-j) : ℚ) -
    (SunCubic.entry 3 n j : ℚ) * (SunCubic.entry 3 n (n+l-j) : ℚ)
  have point (j : ℕ) : c j = (if l ≤ j ∧ j ≤ n then u j else 0) +
      (if j=l-1 then gain else 0) - (if j=n then loss else 0) := by
    by_cases hj1 : j=l-1
    · subst j
      have hsub : n+l-(l-1) = n+1 := by omega
      simp only [c,u,gain,loss,entryAll,hsub,mul_pow]
      split_ifs <;> first | omega | ring
    by_cases hjn : j=n
    · subst j
      simp only [c,u,gain,loss,entryAll,mul_pow,show n+l-n=l by omega]
      split_ifs <;> first | omega | ring
    by_cases hlow : l ≤ j
    · by_cases hhigh : j ≤ n
      · simp only [c,u,entryAll,if_neg hj1,if_neg hjn,if_pos hhigh,if_pos (And.intro hlow hhigh)]
        split_ifs <;> first | omega | ring
      · simp only [c,entryAll,if_neg hj1,if_neg hjn,if_neg hhigh,if_neg (show ¬ (l ≤ j ∧ j ≤ n) by omega)]
        split_ifs <;> first | omega | ring
    · simp only [c,entryAll,if_neg hj1,if_neg hjn,if_neg (show ¬ (l ≤ j ∧ j ≤ n) by omega)]
      split_ifs <;> first | omega | ring
  have norm (j : ℕ) : S*u j = raw n (n+l) j :=
    scaledTerm n j (n+l-j) (by omega)
  calc
    _ = ∑ j ∈ range (n+l+1), S*c j := by
      simp only [SunCubic.delta, SunCubic.prodCoeff, Int.cast_sub, Int.cast_sum, Int.cast_mul]
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    _ = (∑ j ∈ range (n+l+1), if l ≤ j ∧ j ≤ n then raw n (n+l) j else 0) +
          S*gain - S*loss := by
      simp only [point,mul_sub,mul_add,mul_ite,mul_zero,norm,Finset.sum_add_distrib,Finset.sum_sub_distrib]
      simp [Finset.mem_range] <;> omega
    _ = _ := by
      rw [upperRestrict (raw n (n+l)) n l hle, symRestricted n l hle]
      have hw : w n (n+l) n = (bq (n-1) n * bq (n-1) l)^3 := by simp [w,bq]
      dsimp only [gain,loss]
      rw [upperEndGain n l hl hle, upperEndLoss n l hl hle, hw]
      dsimp only [S,upperCorr]
      ring

end Cone

namespace Cone

def truncS4 (r : ℚ) : ℚ := r*(r+1)*(r+2)*(3*r^2+6*r-4)/240

private theorem ascWeight (n d j : ℕ) (hn : 0<n) (hj : 2*j+1≤d) :
    w n d j ≤ w n d (j+1) := by
  obtain ⟨p,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hbal := balance p d j (by omega)
  have hw : 0 ≤ w (p+1) d j := by unfold w; positivity
  have hp : 1 ≤ ((p+1:ℕ):ℚ) := by exact_mod_cast (show 1≤p+1 by omega)
  have hjq : 2*(j:ℚ)+1 ≤ d := by exact_mod_cast hj
  have hbase : ((j:ℚ)+1)*(((p+1:ℕ):ℚ)+d-((j:ℚ)+1)) ≤ (((p+1:ℕ):ℚ)+j)*((d:ℚ)-j) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hjq)]
  have hpos : (0:ℚ) < ((p+1:ℕ):ℚ)+d-(j+1) := by
    have hj0 : (0:ℚ) ≤ j := by positivity
    linarith
  have hpos' : (0:ℚ) < ((j:ℚ)+1)*(((p+1:ℕ):ℚ)+d-(j+1)) := by positivity
  have hmono := pow_le_pow_left₀ hpos'.le hbase 3
  dsimp only [birth,death] at hbal
  simp only [Nat.cast_add, Nat.cast_one] at hbal hmono hpos'
  exact le_of_mul_le_mul_right ((mul_le_mul_of_nonneg_left hmono hw).trans_eq hbal)
    (pow_pos hpos' 3)

private theorem leftWeight (n d l k : ℕ) (hn : 0<n) (hk : 2*(l+k)≤d) :
    w n d l ≤ w n d (l+k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    exact (ih (by omega)).trans (ascWeight n d (l+k) hn (by omega))

theorem endpointWeight (n l j : ℕ) (hn : 0<n) (hl : l≤j) (hj : j≤n) :
    w n (n+l) n ≤ w n (n+l) j := by
  have hs (k : ℕ) (hk : k≤n+l) : w n (n+l) (n+l-k) = w n (n+l) k := by
    unfold w
    rw [show n+l-(n+l-k)=k by omega,mul_comm]
  have he : w n (n+l) n = w n (n+l) l := by
    simpa only [Nat.add_sub_cancel_right] using hs l (by omega)
  rw [he]
  by_cases hx : 2*j≤n+l
  · simpa only [show l+(j-l)=j by omega] using leftWeight n (n+l) l (j-l) hn (by omega)
  · rw [← hs j (by omega)]
    simpa only [show l+(n-j)=n+l-j by omega] using leftWeight n (n+l) l (n-j) hn (by omega)

private def fourthPrim (x : ℚ) : ℚ := x^5/5-x^4/2+x^3/3-x/30

theorem quarticSum (r : ℕ) : (∑ i ∈ Finset.range (r+1), ((i:ℚ)-(r:ℚ)/2)^4) = truncS4 r := by
  let g (i : ℕ) := fourthPrim ((i:ℚ)-(r:ℚ)/2)
  have h (i : ℕ) : g (i+1)-g i = ((i:ℚ)-(r:ℚ)/2)^4 := by
    dsimp only [g,fourthPrim]
    push_cast
    ring
  have ht := Finset.sum_range_sub g (r+1)
  simp only [h] at ht
  rw [ht]
  dsimp only [g,fourthPrim,truncS4]
  push_cast
  ring

theorem truncatedFourth (n l : ℕ) (hn : 0<n) (hl : l≤n) :
    w n (n+l) n * truncS4 ((n:ℚ)-l) ≤
      ∑ i ∈ Finset.range (n-l+1), w n (n+l) (l+i) * ((xval (n+l) (l+i))^2)^2 := by
  rw [← Nat.cast_sub hl, ← quarticSum (n-l), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hx : ((i:ℚ)-((n-l:ℕ):ℚ)/2)^4 = ((xval (n+l) (l+i))^2)^2 := by
    dsimp only [xval]
    push_cast [Nat.cast_sub hl]
    ring
  rw [hx]
  exact mul_le_mul_of_nonneg_right (endpointWeight n l (l+i) hn (by omega) (by omega)) (sq_nonneg _)

end Cone

namespace Cone

private def TL (b : ℚ) := 3*b^2*(b-1)
private def TG (n b r H : ℚ) := TL b*(rc n b+rd n b*(r/2)^2)-H*(6*b^2-9*b+1+2*(r/2)^2)
private def TS (r : ℚ) := r*(r+1)*(r+2)*(3*r^2+6*r-4)/240
private def TP (n l r b H : ℚ) :=
  let den := (n+l-1)^3
  let e := b^2*(n^6*(4*(2*n+1)*l)^3-n^3*(n+l)^3*(n+l+1)^3*den)
  TG n b r H * TS r * den +
   TL b*(e-2*K n b*(2*n*l)^3*((r+1)/2)*den) -
   2*H*l^3*psiF ((r+1)/2)*den

private def TSOS (u v : ℚ) :=
  (8*u-v^2)^2*(12*u^13*v+102*u^12*v^2+371*u^11*v^3+681*u^10*v^4+407*u^9*v^5)


set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem s1 (u v : ℚ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ -rd (1+u+v) ((1+u+v+(1+u))/2) := by
  dsimp only [rd,K]
  ring_nf
  positivity

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem s2 (u v : ℚ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ TG (1+u+v) ((1+u+v+(1+u))/2) v 0 := by
  dsimp only [TG,TL,rc,rd,K]
  ring_nf
  positivity

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem s3 (u v : ℚ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ TP (1+u+v) (1+u) v ((1+u+v+(1+u))/2) 0 := by
  dsimp only [TP,TG,TL,TS,rc,rd,K,psiF]
  ring_nf
  positivity

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem s4 (u v : ℚ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ TG (1+u+v) ((1+u+v+(1+u))/2) v (-rb (1+u+v) ((1+u+v+(1+u))/2)) := by
  dsimp only [TG,TL,rb,rc,rd,K]
  ring_nf
  positivity

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem s5 (u v : ℚ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ TP (1+u+v) (1+u) v ((1+u+v+(1+u))/2) (-rb (1+u+v) ((1+u+v+(1+u))/2)) - TSOS u v := by
  dsimp only [TP,TG,TL,TS,TSOS,rb,rc,rd,K,psiF]
  ring_nf
  positivity
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem tailSigns (u v : ℚ) (hu : 0≤u) (hv : 0≤v) (H : ℚ)
    (hH : H=0 ∨ H= -rb (1+u+v) ((1+u+v+(1+u))/2)) :
    rd (1+u+v) ((1+u+v+(1+u))/2) ≤ 0 ∧
    0 ≤ TG (1+u+v) ((1+u+v+(1+u))/2) v H ∧
    0 ≤ TP (1+u+v) (1+u) v ((1+u+v+(1+u))/2) H := by
  refine ⟨neg_nonneg.mp (s1 u v hu hv), ?_⟩
  rcases hH with rfl | rfl
  · exact ⟨s2 u v hu hv, s3 u v hu hv⟩
  · refine ⟨s4 u v hu hv, ?_⟩
    have left := s5 u v hu hv
    have right : 0 ≤ TSOS u v := by unfold TSOS; positivity
    linarith only [left,right]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem tailCertificate (n l r b : ℚ) (hl : 1≤l) (hr : 0≤r)
    (hn : n=l+r) (hb : b=(n+l)/2) (hb1 : 1<b) :
    ∃ L H G : ℚ, 0<L ∧ 0≤H ∧ 0≤G ∧
    (∀ s : ℚ, 0 ≤ s → s ≤ (r/2)^2 →
      G*s^2 ≤ L*(b^2*F n b s-K n b*Z n b s)-H*ZF b s) ∧
    0≤G*(r*(r+1)*(r+2)*(3*r^2+6*r-4)/240)+L*b^2*upperCorr n l -
       L*K n b*(2*n*l)^3*(r+1)-2*H*l^3*psiF ((r+1)/2) := by
  let H := max 0 (-rb n b)
  have hH0 : 0 ≤ H := le_max_left _ _
  have hBR : 0 ≤ rb n b+H := by
    have hBR' : -rb n b ≤ H := le_max_right _ _
    linarith only [hBR']
  have hH : H=0 ∨ H= -rb n b := by
    rcases le_total (-rb n b) 0 with h | h
    · exact Or.inl (max_eq_left h)
    · exact Or.inr (max_eq_right h)
  let u := l-1
  have hu : 0≤u := sub_nonneg.mpr hl
  have hl' : l=1+u := by dsimp [u]; ring
  have hn' : n=1+u+r := by rw [hn,hl']
  have hb' : b=(1+u+r+(1+u))/2 := by rw [hb,hn',hl']
  have hsign : rd n b ≤ 0 ∧ 0 ≤ TG n b r H ∧ 0 ≤ TP n l r b H := by
    have hH' : H=0 ∨ H= -rb (1+u+r) ((1+u+r+(1+u))/2) := by simpa only [hn',hb'] using hH
    simpa only [hn',hl',hb'] using (tailSigns u r hu hr H hH')
  have hL : 0 < TL b := by
    have : 0 < b-1 := by linarith
    unfold TL
    positivity
  refine ⟨TL b,H,TG n b r H,hL,hH0,hsign.2.1,?_,?_⟩
  · intro s hs hsmax
    have ha := mul_nonneg (mul_nonneg hL.le hBR) hs
    have hc : TL b*rd n b-2*H ≤ 0 := by
      have hneg := mul_nonpos_of_nonneg_of_nonpos hL.le hsign.1
      linarith only [hneg,hH0]
    have he := mul_nonneg (mul_nonneg_of_nonpos_of_nonpos hc (sub_nonpos.mpr hsmax)) (sq_nonneg s)
    have identity : TL b*(b^2*F n b s-K n b*Z n b s)-H*ZF b s - TG n b r H*s^2 =
        TL b*(rb n b+H)*s+(TL b*rd n b-2*H)*(s-(r/2)^2)*s^2 := by
      dsimp only [TL,TG,F,Z,K,ZF,rb,rc,rd]
      ring
    apply sub_nonneg.mp
    rw [identity]
    exact add_nonneg ha he
  · have hden : 0 < n+l-1 := by linarith
    have hm : 0 < n := by linarith
    have hp : 0 < n+1 := by linarith
    have eqn : (TG n b r H * TS r+TL b*b^2*upperCorr n l -
        TL b*K n b*(2*n*l)^3*(r+1)-2*H*l^3*psiF ((r+1)/2))*(n+l-1)^3 =
        TP n l r b H := by
      unfold TP upperCorr
      field_simp [ne_of_gt hm,ne_of_gt hp,ne_of_gt hden]
      <;> ring
    change 0 ≤ TG n b r H * TS r+TL b*b^2*upperCorr n l -
        TL b*K n b*(2*n*l)^3*(r+1)-2*H*l^3*psiF ((r+1)/2)
    have h := hsign.2.2
    rw [← eqn] at h
    exact nonneg_of_mul_nonneg_left h (pow_pos hden 3)

end Cone

namespace Cone
open Finset

private theorem collectTail {I : Finset ℕ} (W S : ℕ → ℚ) (n b L H G : ℚ)
    (hp : ∀ i ∈ I, G*(S i)^2 ≤ L*(b^2*F n b (S i)-K n b*Z n b (S i))-H*ZF b (S i))
    (hw : ∀ i ∈ I, 0 ≤ W i) :
    G*(∑ i ∈ I, W i * (S i)^2) ≤
      L*b^2*(∑ i ∈ I, W i * F n b (S i)) -
      L*K n b*(∑ i ∈ I, W i * Z n b (S i)) -
      H*(∑ i ∈ I, W i * ZF b (S i)) := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have p := mul_le_mul_of_nonneg_left (hp i hi) (hw i hi)
  linarith only [p]

set_option maxHeartbeats 1200000 in
theorem upperHalfDelta (n l : ℕ) (hl : 0 < l) (hle : l ≤ n) :
    0 ≤ SunCubic.delta 3 n (n+l) := by
  have hn : 0 < n := by omega
  by_cases hsmall : n+l ≤ 2
  · have hn1 : n=1 := by omega
    have hl1 : l=1 := by omega
    subst n; subst l; decide
  let b : ℚ := ((n:ℚ)+l)/2
  let r : ℚ := (n:ℚ)-l
  have hNQ : (0:ℚ) < n := by exact_mod_cast hn
  have hr : 0 ≤ r := sub_nonneg.mpr (by exact_mod_cast hle)
  have hb : 1 < b := by
    have hh : (2:ℚ) < (n:ℚ)+l := by exact_mod_cast (show 2<n+l by omega)
    dsimp only [b]; linarith only [hh]
  have hLQ : (1:ℚ) ≤ l := by exact_mod_cast (show 1 ≤ l by omega)
  obtain ⟨L,H,G,hL,hH,hG,hpoint,hpay⟩ :=
    tailCertificate n l r b hLQ hr (by dsimp only [r]; ring) rfl hb
  let I := range (n-l+1)
  let W := fun i : ℕ => w n (n+l) (l+i)
  let S := fun i : ℕ => (xval (n+l) (l+i))^2
  let e := w n (n+l) n
  have he : 0 ≤ e := by dsimp [e,w]; positivity
  have hbound (i : ℕ) (hi : i ∈ I) : S i ≤ (r/2)^2 := by
    have hmax : i+l ≤ n := by have := Finset.mem_range.mp hi; omega
    have hiQ : (i:ℚ)+l ≤ n := by exact_mod_cast hmax
    have h0 : 0 ≤ (i:ℚ) := by positivity
    have ht := mul_nonneg h0 (sub_nonneg.mpr hiQ)
    dsimp only [S,xval,r]
    push_cast
    linarith only [ht]
  have hcollect := collectTail (I:=I) W S n b L H G
    (fun i hi => hpoint _ (sq_nonneg _) (hbound i hi))
    (fun i _ => by dsimp [W,w]; positivity)
  have hm := truncatedFourth n l hn hle
  change e * truncS4 r ≤ ∑ i ∈ I, W i * (S i)^2 at hm
  have hm' := mul_le_mul_of_nonneg_left hm hG
  have hfr := truncatedFranel n l hn hle
  change -2*e*(l:ℚ)^3*psiF ((r+1)/2) ≤ ∑ i ∈ I, W i * ZF b (S i) at hfr
  have hfr' := mul_le_mul_of_nonneg_left hfr hH
  have hc := truncatedCancel n l hn hle
  change (∑ i ∈ I, W i * Z n b (S i)) = -e*(2*(n:ℚ)*l)^3*(r+1) at hc
  rw [hc] at hcollect
  change 0 ≤ G*truncS4 r+L*b^2*upperCorr n l -
       L*K n b*(2*(n:ℚ)*l)^3*(r+1)-2*H*(l:ℚ)^3*psiF ((r+1)/2) at hpay
  have hpay' := mul_nonneg he hpay
  have positiveSum : 0 ≤ L*b^2*((∑ i ∈ I, W i * F n b (S i)) + e * upperCorr n l) := by
    linarith only [hcollect,hm',hfr',hpay']
  have scalePos : 0 < L*b^2 := by positivity
  have Spos := nonneg_of_mul_nonneg_right positiveSum scalePos
  have hI := upperIdentity n l hl hle
  push_cast at hI
  change (n:ℚ)^6*(n+1)^3*(SunCubic.delta 3 n (n+l) : ℚ) =
    (∑ i ∈ I, W i * F n b (S i)) + e * upperCorr n l at hI
  rw [← hI] at Spos
  have scaleN : 0 < (n:ℚ)^6*(n+1)^3 := by positivity
  have hD := nonneg_of_mul_nonneg_right Spos scaleN
  exact_mod_cast hD

end Cone

namespace SunCubic

theorem fullCubic : Conjecture := by
  intro n d hn
  by_cases hlow : d ≤ n
  · simpa only [coeffDelta] using lowerHalf n d hn hlow
  by_cases htop : d ≤ 2*n
  · have ht := Cone.upperHalfDelta n (d-n) (by omega) (by omega)
    rwa [show n+(d-n)=d by omega] at ht
  have out (a b : ℕ) (hab : a+b<d) : prodCoeff 3 a b d = 0 := by
    unfold prodCoeff
    apply Finset.sum_eq_zero
    intro j hj
    by_cases h : j ≤ a
    · have hb : ¬ d-j ≤ b := by omega
      simp [entry,hb]
    · simp [entry,h]
  rw [delta, out (n-1) (n+1) (by omega), out n n (by omega)]
  decide

theorem fullPolynomial (n d : ℕ) (hn : 1 ≤ n) :
    0 ≤ (R 3 (n-1)*R 3 (n+1)-(R 3 n)^2).coeff d := by
  rw [coeffDelta]
  exact fullCubic n d hn

end SunCubic
#print axioms SunCubic.fullPolynomial
