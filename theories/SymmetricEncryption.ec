require import Option.
require import Bool.
require import List.

type key.
type plaintext.
type ciphertext.

module type Scheme = {
  fun init(): unit {*}
  fun kg(): key
  fun enc(k:key,p:plaintext): ciphertext
  fun dec(k:key,c:ciphertext): plaintext option
}.

module type CPA_Oracles = {
  fun enc(p:plaintext): ciphertext
}.

module type CCA_Oracles = {
  fun enc(p:plaintext): ciphertext
  fun dec(c:ciphertext): plaintext option
}.

module type Adv_INDCPA (O:CPA_Oracles) = {
  fun choose(): plaintext * plaintext
  fun guess(c:ciphertext): bool
}.

module type Adv_INDCCA (O:CCA_Oracles) = {
  fun choose(): plaintext * plaintext
  fun guess(c:ciphertext): bool
}.

module Wrap (S:Scheme) = {
  var k:key
  var qs:ciphertext list

  fun init(): unit = {
    S.init();
    k = S.kg();
    qs = [];
  }

  fun enc(p:plaintext): ciphertext = {
    var r:ciphertext;

    r = S.enc(k,p);
    return r;
  }

  fun dec(c:ciphertext): plaintext option = {
    var r:plaintext option;

    qs = c::qs;
    r = S.dec(k,c);
    return r;
  }

  fun queried_challenge(c:ciphertext): bool = {
    return mem c qs;
  }
}.

module INDCPA (S:Scheme, A:Adv_INDCPA) = {
  module O = Wrap(S)
  module A = A(O)

  fun main(): bool = {
    var b, b':bool;
    var p, p0, p1:plaintext;
    var c:ciphertext;

    O.init();
    (p0,p1) = A.choose();
    b = ${0,1};
    p = if b then p1 else p0;
    c = O.enc(p);
    b' = A.guess(c);
    return (b = b');
  }
}.

module INDCCA (S:Scheme, A:Adv_INDCCA) = {
  module O = Wrap(S)
  module A = A(O)

  fun main(): bool = {
    var b, b', qc:bool;
    var p, p0, p1:plaintext;
    var c:ciphertext;

    O.init();
    (p0,p1) = A.choose();
    b = ${0,1};
    p = if b then p1 else p0;
    c = O.enc(p);
    b' = A.guess(c);
    qc = O.queried_challenge(c);
    return (b = b' /\ !qc);
  }
}.

module ToCCA (A:Adv_INDCPA, O:CCA_Oracles) = A(O).

lemma CCA_implies_CPA (S <: Scheme {INDCPA}) (A <: Adv_INDCPA {S, INDCPA}) &m:
  Pr[INDCPA(S,A).main() @ &m: res] = Pr[INDCCA(S,ToCCA(A)).main() @ &m: res].
proof strict.
equiv_deno (_: ={glob A} ==> ={res})=> //; fun.
call{2} (_: Wrap.qs = [] ==> !res); first by fun; skip; smt.
conseq (_: _ ==> Wrap.qs{2} = [] /\ (b = b'){1} = (b = b'){2}); first smt.
call (_: ={glob Wrap, glob S} /\ Wrap.qs{2} = []);
  first by fun; call (_: true).
call (_: ={glob Wrap, glob S});
  first by call (_: true).
wp; rnd.
call (_: ={glob Wrap, glob S} /\ Wrap.qs{2} = []);
  first by fun; call (_: true).
by call (_: true ==> ={glob Wrap, glob S} /\ Wrap.qs{2} = []);
     first by fun; wp; eqobs_in.
qed.
