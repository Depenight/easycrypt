(* -------------------------------------------------------------------- *)
require import AllCore Ring StdBigop StdOrder.
require (*--*) Subtype.
(*---*) import Bigint IntID IntOrder.

(* -------------------------------------------------------------------- *)
abstract theory Poly.
type coeff, poly.

clone import IDomain as Coeff with type t <- coeff.

type prepoly = int -> coeff.

inductive ispoly (p : prepoly) =
| IsPoly of
      (forall c, c < 0 => p c = zeror)
    & (exists d, forall c, (d < c)%Int => p c = zeror).

clone include Subtype
  with type T   <- prepoly,
       type sT  <- poly,
       pred P   <- ispoly,
         op wsT <- (fun _ => zeror)
  rename "insub" as "to_poly"
  rename "val"   as "of_poly".

op "_.[_]" (p : poly) (i : int) = (of_poly p) i.

lemma lt0_coeff p c : c < 0 => p.[c] = zeror.
proof.
by move=> lt0_c; rewrite /"_.[_]"; case: (of_polyP p) => /(_ _ lt0_c).
qed.

op deg (p : poly) = argmin idfun (fun i =>
  p.[i] = zeror /\ exists j, j < i /\ p.[j] <> zeror).

lemma gtdeg_coeff (p : poly) (c : int) : deg p < c => p.[c] = zeror.
proof. admitted.

op prepolyC  (c   : coeff) = fun i => if i = 0 then c else zeror.
op prepolyXn (k   : int  ) = fun i => if 0 <= k /\ i = k then oner else zeror.
op prepolyD  (p q : poly ) = fun i => p.[i] + q.[i].
op prepolyN  (p   : poly ) = fun i => - p.[i].

lemma ispolyC (c : coeff) : ispoly (prepolyC c).
proof.
split=> @/prepolyC [c' _|]; first by rewrite ltr_eqF.
by exists 0 => c' gt1_c'; rewrite gtr_eqF.
qed.

lemma ispolyXn (k : int) : ispoly (prepolyXn k).
proof.
split=> @/prepolyXn [c lt0_c|].
+ by case: (0 <= k) => //= ge0_k; rewrite ltr_eqF //#.
+ by exists k => c gt1_c; rewrite gtr_eqF.
qed.

lemma ispolyN (p : poly) : ispoly (prepolyN p).
proof.
split=> @/prepolyN [c lt0_c|]; first by rewrite oppr_eq0 lt0_coeff.
by exists (deg p) => c => /gtdeg_coeff ->; rewrite oppr0.
qed.

lemma ispolyD (p q : poly) : ispoly (prepolyD p q).
proof.
split=> @/prepolyD [c lt0_c|]; first by rewrite !lt0_coeff // addr0.
by exists (max (deg p) (deg q)) => c le; rewrite !gtdeg_coeff ?addr0 //#.
qed.

op polyC  c   = to_polyd (prepolyC  c).
op polyXn k   = to_polyd (prepolyXn k).
op polyN  p   = to_polyd (prepolyN  p).
op polyD  p q = to_polyd (prepolyD  p q).

abbrev poly0 = polyC  zeror.
abbrev poly1 = polyC  oner.
abbrev polyX = polyXn 1.
abbrev ( + ) = polyD.
abbrev [ - ] = polyN.
abbrev ( - ) = fun p q => p + (-q).

lemma coeffE p k : ispoly p => (to_polyd p).[k] = p k.
proof. by move=> ?; rewrite /"_.[_]" to_polydK. qed.

lemma polyCE c k : (polyC c).[k] = if k = 0 then c else zeror.
proof. by rewrite coeffE 1:ispolyC. qed.

lemma poly0E k : poly0.[k] = zeror.
proof. by rewrite polyCE if_same. qed.

lemma polyNE p k : (-p).[k] = - p.[k].
proof. by rewrite coeffE 1:ispolyN. qed.

lemma polyDE p q k : (p + q).[k] = p.[k] + q.[k].
proof. by rewrite coeffE 1:ispolyD. qed.

end Poly.
