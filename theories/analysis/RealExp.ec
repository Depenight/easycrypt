(* -------------------------------------------------------------------- *)
require import Fun Int IntExtra Real RealExtra StdRing StdOrder.
(*---*) import RField RealOrder.

(* -------------------------------------------------------------------- *)
op exp : real -> real.
op ln  : real -> real.

axiom exp0     : exp 0%r = 1%r.
axiom expD     : forall (x y : real), exp (x + y) = exp x * exp y.
axiom exp_mono : forall (x y : real), (exp x <= exp y) <=> (x <= y).
axiom exp_gt0  : forall x, 0%r < exp x.
axiom ln_le0   : forall x, x <= 0%r => ln x = 0%r.

axiom lnK  : forall x, ln (exp x) = x.
axiom expK : forall x, 0%r < x => exp (ln x) = x.

op log (a : real) = fun x => ln x / ln a.

op log10 x = log 10%r x.
op log2  x = log  2%r x.

op e : real = exp 1%r.

axiom ge2_e : 2%r <= e.
axiom lt3_e : e < 3%r.

lemma nosmt e_boundW : 2%r <= e <= 3%r.
proof. by rewrite ge2_e /= ltrW ?lt3_e. qed.

lemma nosmt e_gt0 : 0%r < e.
proof. by apply/(@ltr_le_trans 2%r)/ge2_e. qed.

lemma nosmt e_ge0 : 0%r <= e.
proof. by apply/ltrW/e_gt0. qed.

lemma nosmt ln0 : ln 0%r = 0%r.
proof. by rewrite ln_le0. qed.

lemma nosmt inj_exp : injective exp.
proof. by apply/mono_inj/exp_mono. qed.

lemma nosmt exp_mono_ltr (x y : real): (exp x < exp y) <=> (x < y).
proof. by apply/lerW_mono/exp_mono. qed.

lemma nosmt ln1 : ln 1%r = 0%r.
proof. by rewrite -exp0 lnK. qed.

lemma nosmt lnM (x y : real) : 0%r < x => 0%r < y =>
  ln (x * y) = ln x + ln y.
proof.
move=> gt0x gt0y; apply/inj_exp; rewrite expK ?pmulr_lgt0 //.
by rewrite expD !expK.
qed.

lemma nosmt ln_ge0 (x:real): 1%r <= x => 0%r <= ln x.
proof. admitted.

(* -------------------------------------------------------------------- *)
op ( ^ ) (x a : real) =
  if x < 0%r then b2r (a = 0%r) else exp (a * ln x).

(* -------------------------------------------------------------------- *)
lemma rpowE (x a : real) : 0%r <= x => x^a = exp (a * ln x).
proof. by rewrite /(^) ltrNge => ->. qed.

lemma rpoweE (a : real) : e^a = exp a.
proof. by rewrite rpowE 1:e_ge0 // lnK mulr1. qed.

lemma rpoweK (x : real) : 0%r < x => e^(ln x) = x.
proof. by rewrite rpoweE; apply/expK. qed.

lemma rpowe_mono (n m:real): e^n <= e^m <=> n <= m.
proof. by rewrite !rpoweE exp_mono. qed.

lemma rpowe_hmono (n m:real): n <= m => e^n <= e^m.
proof. by rewrite rpowe_mono. qed.

lemma le_rpow (x y n : real):
  0%r <= n => 0%r <= x <= y => x ^ n <= y ^ n.
proof. admit. qed.

(* -------------------------------------------------------------------- *)
lemma rpow0 x : x^0%r = 1%r.
proof. by rewrite /(^); case: (x < 0%r)=> // _; rewrite mul0r exp0. qed.

lemma rpowD (x n m : real) : x^(n + m) = x^n * x^m.
proof. admit. qed.

lemma rpowM (x n m : real) : x^(n * m) = (x^n)^m.
proof. admit. qed.

lemma rpowMr (x y n : real) : (x*y)^n = x^n * y^n.
proof. admit. qed.

lemma rpowVr (x n : real) : x <> 0%r => (inv x)^n = inv (x^n).
proof. admit. qed.

lemma rpowMVr (x y n : real): y <> 0%r => (x/y)^n = x^n/y^n.
proof. admit. qed.

lemma rpow_gt0 (x n : real): 0%r <= x => 0%r < x^n.
proof. by move/rpowE=> ->; apply/exp_gt0. qed.

lemma rpow_ge0 (x n : real): 0%r <= x => 0%r <= x^n.
proof. by move/rpow_gt0/(_ n)/ltrW. qed.

lemma nosmt le1Dx_rpowe (x : real): 0%r <= x => 1%r+x <= e^x.
proof. admit. qed.

lemma nosmt rpow_hmono (x n m : real) :
  1%r <= x => 0%r <= n <= m => x^n <= x^m.
proof. admit. qed.

lemma rpow_nat x n : 0 <= n => x^(n%r) = x^n.
proof. admit. qed.

(* -------------------------------------------------------------------- *)
require import StdBigop.
(*---*) import Bigreal BRA BRM.

lemma exp_sum (P : 'a -> bool) (F : 'a -> real) s:
  exp (BRA.big P F s) = BRM.big P (fun a => exp (F a)) s.
proof.
elim: s => [|x s ih]; rewrite !(big_nil, big_cons) ?exp0 //.
by case: (P x)=> // Px; rewrite expD ih.
qed.

lemma rpowe_sum (P : 'a -> bool) (F : 'a -> real) s:
  e^(BRA.big P F s) = BRM.big P (fun a => e^(F a)) s.
proof. by rewrite rpoweE exp_sum; apply/eq_bigr=> x _ /=; rewrite rpoweE. qed.